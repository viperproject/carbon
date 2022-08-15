package viper.carbon.modules.impls

import viper.carbon.modules.LoopModule
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.verifier.Verifier
import Implicits._
import viper.carbon.modules.components.StmtComponent
import viper.carbon.utility._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.cfg.utility.{IdInfo, LoopDetector, LoopInfo}
import viper.silver.verifier.{PartialVerificationError, errors}

import scala.collection.mutable
import scala.collection.mutable.Map
import scala.collection.immutable.{Map => ImmutableMap}


/**
  * Info used to indicate that statement was solely added for having an AST that is easier to work with for the handling
  * of loops. Thus, the statement can be ignored. It must be guaranteed that any statement containing this info object,
  * does not change the meaning of the program even if it is not ignored ("inhale true" would, for example, be ok)
  */
case class LoopDummyStmtInfo() extends sil.Info {
  override def comment: Seq[String] = Seq(toString)

  override def isCached: Boolean = false
}

class DefaultLoopModule(val verifier: Verifier) extends LoopModule with StmtComponent {

  import verifier._
  import inhaleModule._
  import exhaleModule._
  import expModule._
  import permModule._
  import heapModule._

  implicit val namespace = verifier.freshNamespace("loop")

  //separate masks for each loop to store the permissions which are framed away
  private var frames: Map[Int, (LocalVarDecl,LocalVarDecl)] = Map[Int, (LocalVarDecl, LocalVarDecl)]();

  private var loopToInvs: Map[Int, Seq[sil.Exp]] = Map.empty
  private var labelLoopInfoMap: Map[String, LoopInfo] = Map.empty
  private var loopToWrittenVars: ImmutableMap[Int, Seq[sil.LocalVar]] = ImmutableMap.empty

  private var nodeToCondLoopInfoOutput : Map[Int, Seq[LoopGenKind]] = Map.empty
  private var nodeToLoopInfoOutput : Map[Int, Seq[LoopGenKind]] = Map.empty

  private val sumMaskName : Identifier = Identifier("LoopSumMask")(namespace)
  private val sumMask = LocalVar(sumMaskName, maskType)

  private val sumHeapName : Identifier = Identifier("LoopSumHeap")(namespace)
  private val sumHeap = LocalVar(sumHeapName, heapType)

  private var currentMethodIsAbstract = false;
  private var usedLoopDetectorOnce = false;
  private var useLoopDetector = false;

  override def start() = {
    /* loopModule should be after all other modules, since it needs to output code that must be output before due to
     * an incoming conditional edge or output after due to an outgoing unconditional edge. Furthermore, the loop module
     * is responsible for handling gotos, which should also happen after the remaining code.
     */
    stmtModule.register(this, after = Seq(verifier.wandModule,verifier.heapModule,verifier.permModule, verifier.stmtModule))
  }

  override def initializeMethod(m: sil.Method): sil.Method = {
    reset()

    //only run the loop detector if the loop body has goto statements
    val hasGotos =
      m.body.fold(false)(body => body.existsDefined(
        {
          case _: sil.Goto => true
        }
      ))

    if(hasGotos) {
      usedLoopDetectorOnce = true
      useLoopDetector = true
      initializeMethodWithGotos(m)
    } else {
      useLoopDetector = false
      m
    }
  }

  private def initializeMethodWithGotos(m: sil.Method): sil.Method = {
    def isComposite(s: sil.Stmt): Boolean = {
      s match {
        case sil.Seqn(_, _) => true
        case sil.If(_, _, _) => true
        case sil.While(_, _, _) => true
        case _ => false
      }
    }

    def getFirstSimple(s: Seq[sil.Stmt]): Option[sil.Stmt] = {
      if (s.isEmpty) {
        None
      } else {
        Some(s(0))
      }
    }

    def getDummyNode(): sil.Stmt = {
      sil.Inhale(sil.TrueLit()(sil.NoPosition, sil.NoInfo, sil.NoTrafos))(sil.NoPosition, LoopDummyStmtInfo(), sil.NoTrafos)
    }

    def getLoopInfo(s: sil.Stmt) : Option[LoopInfo] = s.info.getUniqueInfo[LoopInfo]
    def getIdInfo(s: sil.Stmt) : Option[IdInfo] = s.info.getUniqueInfo[IdInfo]

    def updateMapSeq[K,V](m: mutable.Map[K, Seq[V]], key: K, value: Seq[V]): Unit = {
      m.get(key) match {
        case Some(vOld) => m.put(key, vOld ++ value)
        case None => m.put(key, value)
      }
    }

    def addLoopEdgeKind(stmtId: Int, value: Seq[LoopGenKind], conditionalJump: Boolean): Unit = {
      if(value.nonEmpty) {
        if(conditionalJump) {
          updateMapSeq(nodeToCondLoopInfoOutput, stmtId, value)
        } else {
          updateMapSeq(nodeToLoopInfoOutput, stmtId, value)
        }
      }
    }

    /* Add dummy statements to the method body such that LoopDetector behaves properly. For example, this ensures that
     * the first statement of branches in if-statements are non-composite.
     */
    val rewriteDummyStatements: PartialFunction[sil.Node, sil.Node] =
      (node: sil.Node) =>
        node match {
          case seqStmt@sil.Seqn(stmts, decls) => {
            val newStmts =
              if(stmts.nonEmpty) {
                stmts.foldRight(Seq.empty: Seq[sil.Stmt])((a, b) => {
                  if (isComposite(a) && getFirstSimple(b).map(b => isComposite(b)).getOrElse(false)) {
                    a +: getDummyNode() +: b
                  } else {
                    a +: b
                  }
                })
              } else {
                Seq(getDummyNode())
              }

            sil.Seqn(newStmts, decls)(seqStmt.pos, seqStmt.info, seqStmt.errT)
          }
          case ifStmt@sil.If(b, thn, els) => {
            def getNewBranch(stmt: sil.Seqn): sil.Seqn = {
              /**
                * ensure that branch is 1) non-empty,
                *                       2) first statement is not a composite statement
                *                       3) first statement is not a label statement (to make sure that there is only one
                *                       predecessor)
                */
              if (getFirstSimple(stmt.ss).map(firstStmt => isComposite(firstStmt) || firstStmt.isInstanceOf[sil.Label]).getOrElse(true)) {
                sil.Seqn(getDummyNode() +: stmt.ss, stmt.scopedDecls)(stmt.pos, stmt.info, stmt.errT)
              } else {
                stmt
              }
            }

            val newThn = getNewBranch(thn)
            val newElse = getNewBranch(els)

            sil.If(b, newThn, newElse)(ifStmt.pos, ifStmt.info, ifStmt.errT)
          }
          case whileStmt@sil.While(cond, invs, body) => {
            //ensure that first and final statements in body are not composite.
            val bodyLastOk =
              if(isComposite(body.ss.last)) {
                sil.Seqn(body.ss ++ Seq(getDummyNode()), body.scopedDecls)(body.pos, body.info, body.errT)
              } else {
                body
              }

            val bodyFirstOk =
            if (getFirstSimple(bodyLastOk.ss).map(firstStmt => isComposite(firstStmt)).getOrElse(true)) {
              sil.Seqn(getDummyNode() +: bodyLastOk.ss, bodyLastOk.scopedDecls)(bodyLastOk.pos, bodyLastOk.info, bodyLastOk.errT)
            } else {
              bodyLastOk
            }
            sil.While(cond, invs, bodyFirstOk)(whileStmt.pos, whileStmt.info, whileStmt.errT)
          }
        }


    // gets the first basic statements in s, assuming that there are no empty sil.Seqn nodes
    def getFirstBasicStmts(s: sil.Stmt, b: Boolean) : Seq[(Int, LoopInfo, Boolean)] = {
      s match {
        case sil.Seqn(ss, _) =>
          getFirstBasicStmts(ss(0), b)
        case sw@sil.While(_,_,_) =>
          (getLoopInfo(sw), getIdInfo(sw)) match {
            case (Some(loopInfo), Some(IdInfo(id))) =>
              Seq((id, loopInfo, b))
            case (_,_) => Seq.empty
          }
        case sil.If(_,thn,els) => getFirstBasicStmts(thn, true) ++ getFirstBasicStmts(els, true)
        case basicStmt : sil.Stmt =>
          (getLoopInfo(basicStmt), getIdInfo(basicStmt)) match {
            case (Some(loopInfo), Some(IdInfo(id))) =>
              Seq((id, loopInfo, b))
            case (_,_) => Seq.empty
          }
        case _ => Seq.empty
      }
    }

    //records for each basic statement all of its successor basic statements for which loop code must be generated
    def captureRelevantNextStmts(s: sil.Stmt, l: Seq[(Int, LoopInfo, Boolean)]) : Unit = {
      s match {
        case sil.Seqn(ss, _) =>  {
          ss.foldRight(l)( (a,b) => {
            captureRelevantNextStmts(a,b)
            val temp = getFirstBasicStmts(a, false)
            temp
          })
        }
        case sil.If(_, thn, els) => {
          captureRelevantNextStmts(thn, l)
          captureRelevantNextStmts(els, l)
        }
        case sil.While(_,_,body) => captureRelevantNextStmts(body, Seq.empty)
        case goto@sil.Goto(target) =>
          labelLoopInfoMap.get(target) match {
            case Some(targetLoopInfo) => {
              getIdInfo(goto) match {
                case Some(IdInfo(id)) =>
                  nodeToLoopInfoOutput.put(id, getLoopEdgeKind(getLoopInfo(goto), targetLoopInfo))
                case None =>
                  sys.error("Goto does not have a unique id")
              }
            }
            case _ =>
          }
        case sourceStmt : sil.Stmt =>
          if (l.nonEmpty) {
              getIdInfo(sourceStmt) match {
                case Some(IdInfo(sourceId)) =>
                  l.foreach( a => {
                    val (targetId, targetLoopInfo, conditionalJump) = a
                    if(conditionalJump) {
                      //target cannot have any other predecessors and we need to generate the code after the condition is evaluated
                      addLoopEdgeKind(targetId, getLoopEdgeKind(getLoopInfo(sourceStmt), targetLoopInfo), true)
                    } else {
                      /* target may have other predecessors, but since it's an unconditional jump, we can generate code
                         at the source
                       */
                      addLoopEdgeKind(sourceId, getLoopEdgeKind(getLoopInfo(sourceStmt), targetLoopInfo), false)
                    }
                  })
                case None => sys.error("basic statement, for which next statement contains loop information does not have id")
              }
            }
      }
    }

    val result =
      m.body match {
        case Some(s) =>
          currentMethodIsAbstract = false
          val normalizedBody =
            s.transform(
              rewriteDummyStatements, sil.utility.rewriter.Traverse.BottomUp
            ).asInstanceOf[sil.Seqn]

          val (loopInfoBody, loopToWrittenVarsResult) = LoopDetector.detect(normalizedBody, true, true)
          loopToWrittenVars = loopToWrittenVarsResult.get
          initializeMappings(loopInfoBody)
          captureRelevantNextStmts(loopInfoBody, Seq())
          m.copy(body = Some(loopInfoBody))(m.pos, m.info, m.errT)
        case None =>
          currentMethodIsAbstract = true
          m
      }

    result
  }

  override def isLoopDummyStmt(stmt: sil.Stmt): Boolean =
    stmt.info.getUniqueInfo[LoopDummyStmtInfo].nonEmpty

  override def sumOfStatesAxiomRequired(): Boolean = usedLoopDetectorOnce

  private def relevantForLoops(s: sil.Stmt) : Boolean = {
    s match {
      case node@(_: sil.If | _: sil.Seqn) => false
      case _ => true
    }
  }

  private def initializeMappings(m: sil.Stmt) : Unit = {
    loopToInvs = Map.empty
    labelLoopInfoMap = Map.empty

    def visit[N, A](n: N, subs: N => Seq[N], f: PartialFunction[N, A]): Unit =
      sil.utility.Visitor.visit(n, subs)(f)

    def updateInvariantMap(info: sil.Info, invs: Seq[sil.Exp]): Unit = {
      info.getUniqueInfo[LoopInfo] match {
        case Some(LoopInfo(Some(headId), _)) =>
          loopToInvs = loopToInvs + (headId -> invs)
        case _ =>
      }
    }

    def updateLabelMap(labelName: String, info: sil.Info) = {
      info.getUniqueInfo[LoopInfo] match {
        case Some(loopInfo: LoopInfo) =>
          labelLoopInfoMap = labelLoopInfoMap + (labelName -> loopInfo)
        case None =>
      }
    }

    val f: PartialFunction[sil.Node, Unit] = {
      (stmt: sil.Node) =>
        stmt match {
          case sil.While(_, invs, _) =>
            val (_, info, _) = stmt.meta
            updateInvariantMap(info, invs)
          case lbl@sil.Label(name, invs) =>
            val (_, info, _) = stmt.meta
            updateLabelMap(name, info)
            if(lbl.info.getUniqueInfo[LoopInfo].fold(false)(loopInfo => loopInfo.head.nonEmpty)) {
              updateInvariantMap(info, invs)
            }
        }
    }

    visit(m, sil.utility.Nodes.subnodes, f)
  }

  private def getLoopEdgeKind(sourceOpt: Option[LoopInfo], target: LoopInfo) : Seq[LoopGenKind] = {
    val LoopInfo(targetHeadOpt, targetLoops) = target

    val loopHeadKinds =
    {
      targetHeadOpt match {
        case Some(headId) => {
          //note that if sourceOpt = None, then this means the source loop information is the same as for the target
          if (sourceOpt.fold(true)(source => source.loops.contains(headId))) {
            Seq(Backedge(headId))
          } else {
            /** Since we currently eliminate all backedges, we can generate all the code necessary when jumping to a
             * loop head right at the loop head. Thus, we need not record an "EnterLoop" edge here.
             * If backedges were not eliminated, this would not work (since some part of the shared code should not be
              * executed then, such as storing the mask in the frame after exhaling the invariant).
             */
            //Seq(EnterLoop(headId))
            Seq()
          }
        }
        case None => Seq()
      }
    }

    var exitedLoops : Seq[Int] = Seq()
    sourceOpt match {
      case Some(LoopInfo(_, sourceLoops)) => {
        sourceLoops.foreach {
          (sourceLoopId: Int) =>
            if (targetHeadOpt.fold(true)(targetHeadId => sourceLoopId != targetHeadId) && !targetLoops.contains(sourceLoopId)) {
              //exiting loop
              exitedLoops = sourceLoopId +: exitedLoops
            }
        }
      }
      case None =>
    }

    val result =
      if(exitedLoops.nonEmpty) {
        ExitLoops(exitedLoops) +: loopHeadKinds
      } else {
        loopHeadKinds
      }

    result
  }

  private def handleEdges(edgesKind: Seq[LoopGenKind]): Seq[Stmt] = {
    edgesKind.foldRight[Seq[Stmt]](Seq())( (edgeKind, resultStmt) => {
      edgeKind match {
        case ExitLoops(loopIds) => exitLoops(loopIds) +: resultStmt
        case Backedge(loopId) => backedgeJump(loopId) +: resultStmt
        case BeforeEnterLoop(_) => sys.error("Unexpected edge kind")
      }
    })
  }

  /*
   * return invariants and written variables of loop
   */
  private def getWhileInformation(w: sil.While): (Seq[sil.Exp], Seq[sil.LocalVar]) = {
    if(useLoopDetector) {
      w.info.getUniqueInfo[LoopInfo] match {
        case Some(LoopInfo(Some(loopHeadId), _)) =>
          val invs = getLoopInvariants(loopHeadId)
          /** FIXME
           If loopToWrittenVars.get(loopHeadId).isEmpty evaluates to true, then it may be that the while loop may
           not be a natural loop in the CFG. In this case, it's not clear what the behaviour should be, so we just
           take the written variables via the AST (w.writtenVars).
          */
          val allWrittenVars = loopToWrittenVars.getOrElse(loopHeadId, w.writtenVars)
          /* FIXME
           * Not sure if the RHS of diff makes sense in the "normal" case where the written variables are
           * obtained from the LoopDetector. If syntactic and natural loops coincide, it might be fine.
           */
          val writtenVars = allWrittenVars diff (w.body.transitiveScopedDecls.collect { case l: sil.LocalVarDecl => l } map (_.localVar))
          (invs, writtenVars)
        case _ => sys.error("While loop is not a loop head")
      }
    } else {
        val writtenVars = w.writtenVars diff (w.body.transitiveScopedDecls.collect {case l: sil.LocalVarDecl => l} map (_.localVar))
        (w.invs, writtenVars)
    }
  }

  private def handleWhile(w: sil.While): Stmt = {
        val guard = translateExp(w.cond)
        val (invs, writtenVars) = getWhileInformation(w)

        beforeLoopHead(invs, w.info.getUniqueInfo[LoopInfo].map(loopInfo => loopInfo.head.get)) ++
        MaybeCommentBlock("Havoc loop written variables (except locals)",
          Havoc((writtenVars map translateExp).asInstanceOf[Seq[Var]]) ++
            (writtenVars map (v => mainModule.allAssumptionsAboutValue(v.typ,mainModule.translateLocalVarSig(v.typ, v),false)))
        ) ++
        MaybeCommentBlock("Check definedness of invariant", NondetIf(
          (invs map (inv => inhaleWithDefinednessCheck(inv, errors.ContractNotWellformed(inv)))) ++
            Assume(FalseLit())
        )) ++
        MaybeCommentBlock("Check the loop body", NondetIf({
          val (freshStateStmt, prevState) = stateModule.freshTempState("loop")
          val stmts = MaybeComment("Reset state", freshStateStmt ++ stateModule.initBoogieState) ++
            MaybeComment("Inhale invariant", inhale(invs map (x => (x, errors.WhileFailed(x))), addDefinednessChecks = false) ++ executeUnfoldings(invs, (inv => errors.Internal(inv)))) ++
            Comment("Check and assume guard") ++
            checkDefinedness(w.cond, errors.WhileFailed(w.cond)) ++
            Assume(guard) ++ stateModule.assumeGoodState ++
            MaybeCommentBlock("Translate loop body", stmtModule.translateStmt(w.body)) ++
            MaybeComment("Exhale invariant", executeUnfoldings(invs, (inv => errors.LoopInvariantNotPreserved(inv))) ++ exhale(invs map (e => (e, errors.LoopInvariantNotPreserved(e))))) ++
            MaybeComment("Terminate execution", Assume(FalseLit()))
          stateModule.replaceState(prevState)
          stmts
        }
        )) ++
        MaybeCommentBlock("Inhale loop invariant after loop, and assume guard",
          Assume(guard.not) ++ stateModule.assumeGoodState ++
            inhale(invs map (x => (x, errors.WhileFailed(x))), addDefinednessChecks = false) ++ executeUnfoldings(invs, (inv => errors.Internal(inv)))
        )
  }

  override def handleStmt(s: sil.Stmt, statesStackOfPackageStmt: List[Any] = null, allStateAssms: Exp = TrueLit(), insidePackageStmt: Boolean = false): (Seqn => Seqn) = {
    if(useLoopDetector) {
      handleStmtLoopDetector(s, statesStackOfPackageStmt, allStateAssms,insidePackageStmt)
    } else {
      inner =>
        s match {
          case w@sil.While(_,_,_) => inner ++ handleWhile(w)
          case sil.Goto(_) => sys.error("Loop Module is incorrectly initialized: Goto is translated, but loop detector is not used")
          case _ => inner
        }
    }
  }

  private def handleStmtLoopDetector(s: sil.Stmt, statesStackOfPackageStmt: List[Any] = null, allStateAssms: Exp = TrueLit(), insidePackageStmt: Boolean = false): (Seqn => Seqn) = {
    inner => {
      if (relevantForLoops(s)) {
        val stmtId = s.info.getUniqueInfo[IdInfo]
        stmtId match {
          case Some(IdInfo(id)) => {
            //code related to incoming edges
            val incomingEdges = nodeToCondLoopInfoOutput.get(id).fold[Seq[Stmt]](Seq())(edgesKind => {
              handleEdges(edgesKind)
            })

            //loop head code
            val loopHead =
              if (s.isInstanceOf[sil.While]) {
                Seq(handleWhile(s.asInstanceOf[sil.While]))
              } else {
                s.info.getUniqueInfo[LoopInfo] match {
                  case Some(LoopInfo(Some(loopId), _)) =>
                    Seq(loopInit(loopId))
                  case _ => Seq()
                }
              }

            //code related to outgoing edges
            val outgoingEdges = nodeToLoopInfoOutput.get(id).fold[Seq[Stmt]](Seq())(edgesKind => {
              handleEdges(edgesKind)
            })
            val isBackedge = nodeToLoopInfoOutput.get(id).fold(false)(edgesKind => edgesKind.exists(edgeKind => edgeKind.isInstanceOf[Backedge]))

            /* if statement is a goto, then it must be output at the end, otherwise code will not be reachable in Boogie
     */
            incomingEdges ++ inner ++ loopHead ++ outgoingEdges ++
              (s match {
                case sil.Goto(target) if !isBackedge => {
                  Seq(Goto(Lbl(Identifier(target)(stmtModule.labelNamespace))))
                }
                case _ => Seq()
              })
          }
          case None =>
            /* This can occur whenever a statement is translated that was not part of the original body. */
            inner
        }
      } else {
        inner
      }
    }
  }

  private def loopInit(loopId: Int): Stmt = {
    val invs : Seq[sil.Exp] = getLoopInvariants(loopId)
    val writtenVars : Seq[sil.LocalVar] = getWrittenVariables(loopId)

    //this sharing of code before loop head only works with backedge elimination with the current approach
    beforeLoopHead(invs, Some(loopId)) ++
    MaybeCommentBlock("Code for loop head " + loopId,
      MaybeCommentBlock("Havoc loop written variables (except locals)",
        Havoc((writtenVars map translateExp).asInstanceOf[Seq[Var]]) ++
          (writtenVars map (v => mainModule.allAssumptionsAboutValue(v.typ, mainModule.translateLocalVarSig(v.typ, v), false)))
      ) ++
        MaybeCommentBlock("Check definedness of invariant", NondetIf(
        (invs map (inv => inhaleWithDefinednessCheck(inv, errors.ContractNotWellformed(inv)))) ++
          Assume(FalseLit())
      )) ++
      MaybeCommentBlock("Check the loop body",
        /** FIXME: here we change the state without resetting it
            As long as modules the state at this point refers to the original state, this is fine.
         */
          MaybeComment("Reset state", stateModule.initBoogieState) ++
          MaybeComment("Inhale invariant", inhale(invs map (x => (x, errors.WhileFailed(x))), addDefinednessChecks = false) ++ executeUnfoldings(invs, (inv => errors.Internal(inv))))
      )
    )
  }

  private def backedgeJump(loopId: Int): Stmt = {
    val invs : Seq[sil.Exp] = getLoopInvariants(loopId)
    MaybeCommentBlock("Backedge to loop " + loopId,
      MaybeCommentBlock("Check definedness of invariant", NondetIf(
        (invs map (inv => inhaleWithDefinednessCheck(inv, errors.ContractNotWellformed(inv)))) ++
          Assume(FalseLit())
      )) ++
      MaybeComment("Exhale invariant", executeUnfoldings(invs, (inv => errors.LoopInvariantNotPreserved(inv))) ++ exhale(invs map (e => (e, errors.LoopInvariantNotPreserved(e))))) ++
        MaybeComment("Terminate execution", Assume(FalseLit()))
    )
  }

  private def beforeLoopHead(invs: Seq[sil.Exp], loopIdOpt: Option[Int]): Stmt = {
    MaybeCommentBlock("Before loop head" + loopIdOpt.fold("")(i => Integer.toString(i)),
      MaybeCommentBlock("Exhale loop invariant before loop",
        executeUnfoldings(invs, (inv => errors.LoopInvariantNotEstablished(inv))) ++ exhale(invs map (e => (e, errors.LoopInvariantNotEstablished(e))))
      ) ++
        loopIdOpt.fold(Nil:Stmt)(loopId => {
          val (frameMask, frameHeap) = getFrame(loopId)
          MaybeCommentBlock("Store frame in mask associated with loop",
            Seq(Assign(frameMask.l, currentMask(0)),
                Assign(frameHeap.l, currentHeap(0))
            )
          )
        } )
    )
  }

  private def exitLoops(loopIds: Seq[Int]): Stmt = {
    if(loopIds.isEmpty) {
      sys.error("Exit loop without any loop identifiers")
    } else {
      MaybeCommentBlock("Exiting loops " + loopIds.foldLeft("")((output, i) => output + ", " + i),
        loopIds.foldLeft[Stmt](Nil)((curStmt, loopId) => {
            val (frameMask, frameHeap) = getFrame(loopId)
            curStmt ++
              // sum masks and heaps
              Seq(
                Havoc(Seq(sumHeap)),
                Havoc(Seq(sumMask)),
                Assume(heapModule.sumHeap(sumHeap, currentHeap(0), currentMask(0), frameHeap.l, frameMask.l)),
                Assign(currentHeap(0), sumHeap),
                Assume(permModule.sumMask(Seq(sumMask), currentMask, Seq(frameMask.l))),
                Assign(currentMask(0), sumMask),
                stateModule.assumeGoodState
              )
          })
      )
    }
  }

  override def name: String = "Loop module"

  override def reset(): Unit = {
    frames = Map.empty
    nodeToLoopInfoOutput = Map.empty
    nodeToCondLoopInfoOutput = Map.empty
    loopToInvs = Map.empty
    loopToWrittenVars = ImmutableMap.empty
    useLoopDetector = false
  }

  private def getFrame(loopId: Int): (LocalVarDecl, LocalVarDecl) = {
    frames.get(loopId) match {
      case Some(fMask) => fMask
      case None => {
        val freshMaskDecl = LocalVarDecl(Identifier("frameMask" + loopId), permModule.maskType)
        val freshHeapDecl = LocalVarDecl(Identifier("frameHeap" + loopId), heapModule.heapType)
        frames += (loopId -> (freshMaskDecl, freshHeapDecl))
        (freshMaskDecl, freshHeapDecl)
      }
    }
  }

  private def getLoopInvariants(loopId: Int): Seq[sil.Exp] = {
    loopToInvs.get(loopId) match {
      case Some(invs) => invs
      case None => sys.error("DefaultLoopModule: loop id " + loopId + " not registered")
    }
  }

  private def getWrittenVariables(loopId: Int): Seq[sil.LocalVar] = {
    loopToWrittenVars.get(loopId) match {
      case Some(localVars) => localVars
      case None => throw new RuntimeException("DefaultLoopModule: loop id is not registered")
    }
  }

  //FIXME: duplicated from DefaultStmtModule
  private def executeUnfoldings(exps: Seq[sil.Exp], exp_error: (sil.Exp => PartialVerificationError)): Stmt = {
    (exps map (exp => (if (exp.existsDefined[Unit]({case sil.Unfolding(_,_) => })) checkDefinedness(exp, exp_error(exp), false) else Nil:Stmt)))
  }

}

