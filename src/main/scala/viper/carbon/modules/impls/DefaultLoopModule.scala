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

  implicit val namespace = verifier.freshNamespace("loop")

  //separate masks for each loop to store the permissions which are framed away
  private var framedMasksLoops: Map[Int, LocalVarDecl] = Map[Int, LocalVarDecl]();

  private var loopToInvs: Map[Int, Seq[sil.Exp]] = Map.empty
  private var labelLoopInfoMap: Map[String, LoopInfo] = Map.empty
  private var loopToWrittenVars: ImmutableMap[Int, Seq[sil.LocalVar]] = ImmutableMap.empty

  private var nodeToCondLoopInfoOutput : Map[Int, Seq[LoopGenKind]] = Map.empty
  private var nodeToLoopInfoOutput : Map[Int, Seq[LoopGenKind]] = Map.empty

  private val sumMaskName : Identifier = Identifier("LoopSumMask")(namespace)
  private val sumMask = LocalVar(sumMaskName, maskType)

  //if set to false, then loops are translated to Boogie loops and otherwise back edges are cut
  private val cutBackedges = true

  override def start() = {
    /* loopModule should be after all other modules, since it needs to output code that must be output before due to
     * an incoming conditional edge or output after due to an outgoing unconditional edge. Furthermore, the loop module
     * is responsible for handling gotos, which should also happen after the remaining code.
     */
    stmtModule.register(this, after = Seq(verifier.wandModule,verifier.heapModule,verifier.permModule, verifier.stmtModule))
  }

  override def initializeMethod(m: sil.Method): sil.Method = {
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

    /* add dummy statements to the method body such that:
       (1) there are no empty Seqn nodes
       (2) there are no empty then- or else-branches
       (3) before every if-statement there is at least one non-if/non-while statement
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
              if (getFirstSimple(stmt.ss).map(b => isComposite(b)).getOrElse(false)) {
                sil.Seqn(getDummyNode() +: stmt.ss, stmt.scopedDecls)(stmt.pos, stmt.info, stmt.errT)
              } else {
                stmt
              }
            }

            val newThn = getNewBranch(thn)
            val newElse = getNewBranch(els)

            sil.If(b, newThn, newElse)(ifStmt.pos, ifStmt.info, ifStmt.errT)
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
        case sif@sil.If(_,thn,els) => getFirstBasicStmts(thn, true) ++ getFirstBasicStmts(els, true)
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


    val saved = ViperStrategy.forceRewrite
    ViperStrategy.forceRewrite = true

    val result =
      m.body match {
        case Some(s) =>
          val normalizedBody =
            s.transform(
              rewriteDummyStatements, sil.utility.rewriter.Traverse.BottomUp
            ).asInstanceOf[sil.Seqn]

          val (loopInfoBody, loopToWrittenVarsResult) = LoopDetector.detect(normalizedBody, true, true)
          loopToWrittenVars = loopToWrittenVarsResult.get
          initializeMappings(loopInfoBody)
          captureRelevantNextStmts(loopInfoBody, Seq())
          m.copy(body = Some(loopInfoBody))(m.pos, m.info, m.errT)
        case None => m
      }

    ViperStrategy.forceRewrite = saved

    result
  }

  private def mustContainId(s: sil.Stmt) : Boolean = {
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
        case None =>
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
          case sil.Label(name, invs) =>
            val (_, info, _) = stmt.meta
            updateInvariantMap(info, invs)
            updateLabelMap(name, info)
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
            Seq(EnterLoop(headId))
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
        case EnterLoop(loopId) => enterLoop(loopId) +: resultStmt
        case ExitLoops(loopIds) => exitLoops(loopIds) +: resultStmt
        case Backedge(loopId) => backedgeJump(loopId) +: resultStmt
      }
    })
  }

  override def handleStmt(s: sil.Stmt, statesStackOfPackageStmt: List[Any] = null, allStateAssms: Exp = TrueLit(), insidePackageStmt: Boolean = false): (Seqn => Seqn) =
   inner => {
     if(mustContainId(s)) {
       val  stmtId = s.info.getUniqueInfo[IdInfo]
       stmtId match {
         case Some(IdInfo(id)) => {
           //code related to incoming edges
           val incomingEdges = nodeToCondLoopInfoOutput.get(id).fold[Seq[Stmt]](Seq())(edgesKind => { handleEdges(edgesKind) })

           //loop head code
           val loopHead =
             s.info.getUniqueInfo[LoopInfo] match {
               case Some(LoopInfo(Some(loopId), _)) =>
                 Seq(loopInit(loopId))
               case _ => Seq()
             }

           //code related to outgoing edges
           val outgoingEdges = nodeToLoopInfoOutput.get(id).fold[Seq[Stmt]](Seq())(edgesKind => { handleEdges(edgesKind) })
           val isBackedge = nodeToLoopInfoOutput.get(id).fold(false)(edgesKind => edgesKind.exists(edgeKind => edgeKind.isInstanceOf[Backedge]))

           //if statement is a goto, then it must be output at the end, otherwise code will not be reachable in Boogie
           incomingEdges ++ inner ++ loopHead ++ outgoingEdges ++
             (s match {
               case sil.Goto(target) if !cutBackedges || !isBackedge => {
                 Seq(Goto(Lbl(Identifier(target)(stmtModule.labelNamespace))))
               }
               case _ => Seq()
             })
         }
         // this case should never happen
         case None => sys.error("LoopModule: Stmt does not have unique identifier.")
       }
     } else {
       inner
     }
  }

  private def loopInit(loopId: Int): Stmt = {
    val invs : Seq[sil.Exp] = getLoopInvariants(loopId)
    val writtenVars : Seq[sil.LocalVar] = getWrittenVariables(loopId)
    val havocVarsOpt : Stmt =
      if(cutBackedges) {
        MaybeCommentBlock("Havoc loop written variables (except locals)",
          Havoc((writtenVars map translateExp).asInstanceOf[Seq[Var]]) ++
            (writtenVars map (v => mainModule.allAssumptionsAboutValue(v.typ, mainModule.translateLocalVarSig(v.typ, v), false)))
        )
      } else {
        Nil
      }

    MaybeCommentBlock("Code for loop head " + loopId,
        havocVarsOpt ++
      MaybeCommentBlock("Check definedness of invariant", NondetIf(
        (invs map (inv => checkDefinednessOfSpecAndInhale(inv, errors.ContractNotWellformed(inv)))) ++
          Assume(FalseLit())
      )) ++
      MaybeCommentBlock("Check the loop body",
          MaybeComment("Reset state", stateModule.resetBoogieState) ++
          MaybeComment("Inhale invariant", inhale(invs) ++ executeUnfoldings(invs, (inv => errors.Internal(inv)))) ++
          stateModule.assumeGoodState
      )
    )
  }

  private def backedgeJump(loopId: Int): Stmt = {
    val invs : Seq[sil.Exp] = getLoopInvariants(loopId)
    MaybeCommentBlock("Backedge to loop " + loopId,
      MaybeCommentBlock("Check definedness of invariant", NondetIf(
        (invs map (inv => checkDefinednessOfSpecAndInhale(inv, errors.ContractNotWellformed(inv)))) ++
          Assume(FalseLit())
      )) ++
      MaybeComment("Exhale invariant", executeUnfoldings(invs, (inv => errors.LoopInvariantNotPreserved(inv))) ++ exhale(invs map (e => (e, errors.LoopInvariantNotPreserved(e))))) ++
        MaybeComment("Terminate execution", Assume(FalseLit()))
    )
  }

  private def enterLoop(loopId: Int): Stmt = {
    val loopMask: LocalVarDecl = getLoopMask(loopId)
    val invs: Seq[sil.Exp] = getLoopInvariants(loopId)
    MaybeCommentBlock("Before loop head" + loopId,
      MaybeCommentBlock("Check definedness of invariant", NondetIf(
        (invs map (inv => checkDefinednessOfSpecAndInhale(inv, errors.ContractNotWellformed(inv)))) ++
          Assume(FalseLit())
      )) ++
      MaybeCommentBlock("Exhale loop invariant before loop",
        executeUnfoldings(invs, (inv => errors.LoopInvariantNotEstablished(inv))) ++ exhale(invs map (e => (e, errors.LoopInvariantNotEstablished(e))))
      ) ++
      MaybeCommentBlock("Store frame in mask associated with loop",
        Assign(loopMask.l, staticMask(0).l)
      )
    )
  }

  private def exitLoops(loopIds: Seq[Int]): Stmt = {
    if(loopIds.isEmpty) {
      sys.error("Exit loop without any loop identifiers")
    } else {
      MaybeCommentBlock("Exiting loops " + loopIds.foldLeft("")((output, i) => output + " " + i),
        loopIds.foldLeft[Stmt](Nil)((curStmt, id) => {
            curStmt ++
              Seq(
                Havoc(Seq(sumMask)),
                Assume(permModule.sumMask(Seq(sumMask), currentMask, Seq(getLoopMask(id).l))),
                Assign(currentMask(0), sumMask)
              )
          })
      )
    }
  }

  override def name: String = "Loop module"

  override def reset(): Unit = { framedMasksLoops = Map[Int, LocalVarDecl]() }

  private def getLoopMask(loopId: Int): LocalVarDecl = {
    framedMasksLoops.get(loopId) match {
      case Some(fMask) => fMask
      case None => {
        val freshDecl = LocalVarDecl(Identifier("frameMask" + loopId), permModule.maskType)
        framedMasksLoops += (loopId -> freshDecl)
        freshDecl
      }
    }
  }

  private def getLoopInvariants(loopId: Int): Seq[sil.Exp] = {
    loopToInvs.get(loopId) match {
      case Some(invs) => invs
      case None => throw new RuntimeException("DefaultLoopModule: loop id not registered")
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

