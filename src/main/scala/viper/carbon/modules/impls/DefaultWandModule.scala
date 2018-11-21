/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.impls


import viper.carbon.modules._
import viper.carbon.verifier.Verifier
import viper.carbon.boogie._
import viper.carbon.boogie.Implicits._
import viper.silver.ast.utility.Expressions
import viper.silver.ast.MagicWandStructure
import viper.silver.verifier.{reasons, PartialVerificationError}
import viper.silver.{ast => sil}

class
DefaultWandModule(val verifier: Verifier) extends WandModule {
  import verifier._
  import stateModule._
  import permModule._

  val transferNamespace = verifier.freshNamespace("transfer")
  val wandNamespace = verifier.freshNamespace("wands")
  //wands stored
  type WandShape = Func
  //This needs to be resettable, which is why "lazy val" is not used. See also: wandToShapes method
  private var lazyWandToShapes: Option[Map[MagicWandStructure.MagicWandStructure, WandShape]] = None
  /** CONSTANTS FOR TRANSFER START**/

  /* denotes amount of permission to add/remove during a specific transfer */
  val transferAmountLocal: LocalVar = LocalVar(Identifier("takeTransfer")(transferNamespace), permType)

  /*stores amount of permission still needed during transfer*/
  val neededLocal: LocalVar = LocalVar(Identifier("neededTransfer")(transferNamespace),permType)

  /*stores initial amount of permission needed during transfer*/
  val initNeededLocal = LocalVar(Identifier("initNeededTransfer")(transferNamespace), permType)

  /*used to store the current permission of the top state of the stack during transfer*/
  val curpermLocal = LocalVar(Identifier("maskTransfer")(transferNamespace), permType)

  /*denotes the receiver evaluated in the Used state, this is inserted as receiver to FieldAccessPredicates such that
  * existing interfaces can be reused and the transfer can be kept general */

  val rcvLocal: LocalVar = LocalVar(Identifier("rcvLocal")(transferNamespace), heapModule.refType)

  /* boolean variable which is used to accumulate assertions concerning the validity of a transfer*/
  val boolTransferTop = LocalVar(Identifier("accVar2")(transferNamespace), Bool)

  /** CONSTANTS FOR TRANSFER END**/

  /* Gaurav (03.04.15): this seems nicer as an end result in the Boogie program but null for pos,info params is
   * not really nice
   *   val boogieNoPerm:Exp = permModule.translatePerm(sil.NoPerm()(null,null))
  */
  val boogieNoPerm:Exp = RealLit(0)
  val boogieFullPerm:Exp = RealLit(1)

  var mainError: PartialVerificationError = null


  //use this to generate unique names for states
  private val names = new BoogieNameGenerator()


  def name = "Wand Module"

  def wandToShapes: Map[MagicWandStructure.MagicWandStructure, DefaultWandModule.this.WandShape] = {
    val result = lazyWandToShapes match {
      case Some(m) => m
      case None =>
        mainModule.verifier.program.magicWandStructures.map(wandStructure => {
          val wandName = names.createUniqueIdentifier("wand")
          val wandType = heapModule.wandFieldType(wandName)
          //get all the expressions which form the "holes" of the shape,
          val arguments = wandStructure.subexpressionsToEvaluate(mainModule.verifier.program)

          //for each expression which is a "hole" in the shape we create a local variable declaration which will be used
          //for the function corresponding to the wand shape
          var i = 0
          val argsWand = (for (arg <- arguments) yield {
            i = i + 1
            LocalVarDecl(Identifier("arg" + i)(wandNamespace), typeModule.translateType(arg.typ), None)
          })

          val wandFun = Func(Identifier(wandName)(wandNamespace), argsWand, wandType)

          (wandStructure -> wandFun)
        }).toMap
    }
    lazyWandToShapes = Some(result)
    result
  }

  override def reset() = {
    lazyWandToShapes = None

    mainError  = null
  }


  override def preamble = wandToShapes.values.collect({
    case fun@Func(name,args,typ) =>
      val vars = args.map(decl => decl.l)
      val f0 = FuncApp(name,vars,typ)
      val typeDecl: Seq[TypeDecl] = heapModule.wandBasicType(name.preferredName) match {
        case named: NamedType => TypeDecl(named)
        case _ => Nil
      }
      typeDecl ++
        fun ++
        Axiom(MaybeForall(args, Trigger(f0),heapModule.isWandField(f0))) ++
        Axiom(MaybeForall(args, Trigger(f0),heapModule.isPredicateField(f0).not))
    }).flatten[Decl].toSeq

  /*
   * method returns the boogie predicate which corresponds to the magic wand shape of the given wand
   * if the shape hasn't yet been recorded yet then it will be stored
   */
  def getWandRepresentation(wand: sil.MagicWand):Exp = {

    //need to compute shape of wand
    val ghostFreeWand = wand

    //get all the expressions which form the "holes" of the shape,
    val arguments = ghostFreeWand.subexpressionsToEvaluate(mainModule.verifier.program)

    val shape:WandShape = wandToShapes(wand.structure(mainModule.verifier.program))

    shape match {
      case Func(name, _, typ) => FuncApp(name, arguments.map(arg => expModule.translateExp(arg)), typ)
    }
  }

  override def translatePackage(p: sil.Package,error: PartialVerificationError):Stmt = {
    p match {
      case pa@sil.Package(wand, _) => ???
        //this is the implementation of the package statement in the old magic wand syntax, which might serve
        //as inspiration for the implementation of the new syntax
        /*wand match {
          case w@sil.MagicWand(left,right) =>
            mainError = error //set the default error to be used by all operations

            val addWand = inhaleModule.inhale(w)
            val currentState = stateModule.state

            val PackageSetup(hypState, usedState, initStmt) = packageInit(wand, None)

            val curStateBool = LocalVar(Identifier(names.createUniqueIdentifier("boolCur"))(transferNamespace),Bool)
            val stmt = initStmt++(curStateBool := TrueLit()) ++
              exec(hypState :: StateRep(currentState, curStateBool) :: Nil, usedState, right, hypState.boolVar)

            stateModule.replaceState(currentState)

            stmt ++ addWand

          case _ => sys.error("Package only defined for wands.")
        }*/
    }
  }

  /**
   * this function corresponds to the exec function described in the magic wand paper
   * @param states  stack of hypothetical states
   * @param ops state we're constructing, the state should always be set to this state right before a call to exec
   *            and right after the exec call is finished
   * @param e expression in wand which we are regarding, either a ghost operation or an expression without ghost operations
   *          (this should be enforced by the Silver)
   * @param allStateAssms the conjunction of all boolean variables corresponding to the states on the stack
   * @return
   */
  def exec(states: List[StateRep], ops: StateRep, e:sil.Exp, allStateAssms: Exp):Stmt = {
    e match {
      //the ghost operations below (and their AST nodes) no longer exist in the new magic wand syntax
      //parts of the orignal implementation may however be useful when implementing the new syntax.
      /*case fold@sil.FoldingGhostOp(acc,body) =>
        val opsMask = permModule.currentMask
        val opsHeap = heapModule.currentHeap
        val (argsLocal, accTransformed, assignStmt) = evalArgsAccessPredicate(acc, None,mainError,None)

        val predAccTransformed = accTransformed match {
          case pap@sil.PredicateAccessPredicate(_,_) => pap
          case _ =>  sys.error("evalArgsAccessPredicate returned FieldAccessPredicate for input PredicateAccessPredicate")
        }

        val predicateBody = predAccTransformed.loc.predicateBody(verifier.program).get

        val StateSetup(usedState, initStmt) = createAndSetState(None)
        Comment("Translating " + fold.toString()) ++ initStmt ++
          { //get permissions for unfold and then unfold
            val usedOpsAllStatesAssms: Exp = usedState.boolVar&&ops.boolVar&&allStateAssms
            val permForBody = exhaleExt(ops :: states, usedState, predicateBody, usedOpsAllStatesAssms)

            val foldTranslate = stmtModule.translateStmt(sil.Fold(predAccTransformed)(fold.pos, fold.info))
            val foldStmt = If(usedOpsAllStatesAssms, foldTranslate, Statements.EmptyStmt)

            argsLocal.foreach(localVar => mainModule.env.undefine(localVar))

            CommentBlock("Retrieving permissions to execute fold and then folding the predicate",
              assignStmt ++ permForBody ++ foldStmt)
          } ++ {
          //exec in sum state
          val StateSetup(resultState, resultInitStmt) =  createAndSetSumState(opsHeap,opsMask,ops.boolVar,usedState.boolVar)

          resultInitStmt ++ exec(states,resultState, body, allStateAssms)
        }
      case unfold@sil.UnfoldingGhostOp(acc,body) =>
        val opsMask = permModule.currentMask
        val opsHeap = heapModule.currentHeap

        //evaluate arguments of predicate in top state
        val (argsLocal, accTransformed, assignStmt) = evalArgsAccessPredicate(acc, None,mainError,None)

        val StateSetup(usedState, initStmt) = createAndSetState(None)
        Comment("Translating " + unfold.toString()) ++ initStmt ++
          { //get permissions for unfold and then unfold
            val usedOpsAllStatesAssms: Exp = usedState.boolVar&&ops.boolVar&&allStateAssms
            val sil.PredicateAccessPredicate(loc,perm) = acc

            val predAccTransformed = accTransformed match {
              case pap@sil.PredicateAccessPredicate(_,_) => pap
              case _ =>  sys.error("evalArgsAccessPredicate returned FieldAccessPredicate for input PredicateAccessPredicate")
            }

            val permForPred = exhaleExt(ops :: states, usedState, accTransformed, usedOpsAllStatesAssms)
            val unfoldTranslate = stmtModule.translateStmt(sil.Unfold(predAccTransformed)(unfold.pos, unfold.info))

            val unfoldStmt = CommentBlock("unfolding " + acc.toString() ,
              If(usedOpsAllStatesAssms, unfoldTranslate, Statements.EmptyStmt) )

            argsLocal.foreach(localVar => mainModule.env.undefine(localVar))
            CommentBlock("Retrieving permissions to execute unfold and then unfolding the predicate",
              assignStmt ++ permForPred ++ unfoldStmt)
          } ++ {
          //exec in sum state
          val StateSetup(resultState, resultInitStmt) =  createAndSetSumState(opsHeap,opsMask,ops.boolVar,usedState.boolVar)
          resultInitStmt ++ exec(states,resultState, body,allStateAssms)
        }
      case sil.ApplyingGhostOp(wand, body) =>
        wand match {
          case w@sil.MagicWand(left,right) =>
            val opsMask = permModule.currentMask
            val opsHeap = heapModule.currentHeap

            val StateSetup(usedState, initStmt) = createAndSetState(None)
            initStmt ++
              {
                val usedOpsAllStatesAssms: Exp = usedState.boolVar&&ops.boolVar&&allStateAssms

                exhaleExt(ops :: states, usedState, left,usedOpsAllStatesAssms) ++
                  exhaleExt(ops :: states, usedState, wand,usedOpsAllStatesAssms) ++
                  If(usedOpsAllStatesAssms, applyWand(w, mainError), Statements.EmptyStmt)
              } ++ {
              //exec in sum state
              val StateSetup(resultState, resultInitStmt) =  createAndSetSumState(opsHeap,opsMask,ops.boolVar,usedState.boolVar)
              resultInitStmt ++ exec(states,resultState, body,allStateAssms)
            }
          case _ => sys.error("Applying ghost operation only supported for magic wands")
        }
      case p@sil.PackagingGhostOp(wand,body) =>
        val addWand = inhaleModule.inhale(wand)

        val PackageSetup(hypState, usedState, initStmt) = packageInit(wand, None)
        val usedOpsAllStatesAssms: Exp = usedState.boolVar&&ops.boolVar&&allStateAssms

        val execInnerWand = exec(hypState :: ops :: states, usedState, wand.right, hypState.boolVar&&ops.boolVar&&allStateAssms)

        val packaging =  MaybeCommentBlock("Code for the packaging of wand" + wand.toString() +" in" + p.toString(),
          initStmt ++ execInnerWand)

        stateModule.replaceState(ops.state)

        MaybeCommentBlock("Translating " + p.toString(),
          packaging ++ addWand ++ MaybeCommentBlock("Code for body " + body.toString() + " of " + p.toString(), exec(states,ops,body,allStateAssms)) )
          */

      case sil.Let(letVarDecl, exp, body) =>
        val StateRep(_,bOps) = ops
        val translatedExp = expModule.translateExp(exp) // expression to bind "v" to, evaluated in ops state
        val v = mainModule.env.makeUniquelyNamed(letVarDecl) // choose a fresh "v" binder
        mainModule.env.define(v.localVar)
        val instantiatedExp = Expressions.instantiateVariables(body,Seq(letVarDecl),Seq(v.localVar)) //instantiate bound variable

        val stmt =
          (bOps := bOps && (mainModule.env.get(v.localVar) === translatedExp) ) ++
          //GP: maybe it may make more sense to use an assignment here instead of adding the equality as an assumption, but since right now we use all assumptions
          //of states on the state + state ops to assert expressions, it should work
          exec(states,ops,instantiatedExp,allStateAssms)

        mainModule.env.undefine(v.localVar)

        stmt
      case _ =>
        //no ghost operation
        val StateSetup(usedState, initStmt) = createAndSetState(None)
        Comment("Translating exec of non-ghost operation" + e.toString())
        initStmt ++ exhaleExt(ops :: states, usedState,e,ops.boolVar&&allStateAssms)
    }
  }

  /**
   * @param wand wand to be packaged
   * @param boolVar boolean variable to which the newly generated boolean variable associated with the package should
   *                be set to in the beginning
   * @return structure that contains all the necessary blocks to initiate a package
   *
   * Postcondition: state is set to the "Used" state generated in the function
   */
  private def packageInit(wand:sil.MagicWand, boolVar: Option[LocalVar]):PackageSetup = {
    val StateSetup(usedState, initStmt) = createAndSetState(boolVar, "Used", false)

    //inhale left hand side to initialize hypothetical state
    val hypName = names.createUniqueIdentifier("Hyp")
    val StateSetup(hypState,hypStmt) = createAndSetState(None,"Hyp")

    val inhaleLeft = MaybeComment("Inhaling left hand side of current wand into hypothetical state",
      If(hypState.boolVar, expModule.checkDefinednessOfSpecAndInhale(wand.left, mainError), Statements.EmptyStmt))

    stateModule.replaceState(usedState.state)

    PackageSetup(hypState, usedState, hypStmt ++ initStmt ++ inhaleLeft)
  }


  /**
   *
   * @param initBool boolean expression w which the newly generated boolean variable should be initialized
   * @param usedString string to incorporate into unique name for string
   * @param setToNew the state is set to the generated state iff this is set to true
   * @param init if this is set to true then the stmt in UsedStateSetup will initialize the states (for example
   *             masks to ZeroMask), otherwise the states contain no information
   * @return  Structure which can be used at the beginning of many operations involved in the package
   */
  private def createAndSetState(initBool:Option[Exp],usedString:String = "Used",setToNew:Boolean=true,
                                init:Boolean=true):StateSetup = {
    /**create a new boolean variable under which all assumptions belonging to the package are made
      *(which makes sure that the assumptions won't be part of the main state after the package)
      *
      */

    val b = LocalVar(Identifier(names.createUniqueIdentifier("b"))(transferNamespace), Bool)

    val boolStmt =
      initBool match {
        case Some(boolExpr) => (b := boolExpr)
        case _ => Statements.EmptyStmt
      }


    //state which is used to check if the wand holds
    val usedName = names.createUniqueIdentifier(usedString)

    val (usedStmt, currentState) = stateModule.freshEmptyState(usedName,init)
    val usedState = stateModule.state

    val goodState = exchangeAssumesWithBoolean(stateModule.assumeGoodState, b)

    /**DEFINE STATES END **/
    if(!setToNew) {
      stateModule.replaceState(currentState)
    }

    StateSetup(StateRep(usedState,b),usedStmt++boolStmt++goodState)
  }

  /**
   * only heap and mask of one summand state, while current state will be used as second summand
   * @param heapOther heap representation of  summand state
   * @param maskOther mask represenstation of  summand state
   * @param boolOther bool containing facts for summand state
   * @param boolCur bool containing facts for current state
   * @return
   */
  private def createAndSetSumState(heapOther: Seq[Exp], maskOther: Seq[Exp],boolOther:Exp,boolCur:Exp):StateSetup = {
    /*create a state Result which is the "sum" of the current  and Other states, i.e.:
 *1) at each heap location o.f the permission of the Result state is the sum of the permissions
 * for o.f in the current and Other state
 * 2) if the current state has some positive nonzero amount of permission for heap location o.f then the heap values for
 * o.f in the current state and Result state are the same
 * 3) point 2) also holds for the Other state in place of the current state
 *
 * Note: the boolean for the Result state is initialized to the conjunction of the booleans of the current state
   *  and the other state and used (since all facts of each state is transferred)
  */
    val curHeap = heapModule.currentHeap
    val curMask = permModule.currentMask

    val StateSetup(resultState, initStmtResult) =
      createAndSetState(Some(boolOther && boolCur), "Result", true, false)

    val boolRes = resultState.boolVar
    val sumStates = (boolRes := boolRes && permModule.sumMask(maskOther, curMask))
    val equateKnownValues = (boolRes := boolRes && heapModule.identicalOnKnownLocations(heapOther, maskOther) &&
      heapModule.identicalOnKnownLocations(curHeap, curMask))
    val goodState = exchangeAssumesWithBoolean(stateModule.assumeGoodState, boolRes)
    val initStmt =CommentBlock("Creating state which is the sum of the two previously built up states",
      initStmtResult ++ sumStates ++ equateKnownValues ++ goodState)

    StateSetup(resultState, initStmt)

  }

  /*generates code that transfers permissions from states to used such that e can be satisfied
    * Precondition: current state is set to the used state
    * */
  def exhaleExt(states: List[StateRep], used:StateRep, e: sil.Exp, allStateAssms: Exp):Stmt = {
    Comment("exhale_ext of " + e.toString())
    e match {
      case acc@sil.AccessPredicate(_: sil.LocationAccess,_) => transferMain(states,used, e, allStateAssms)
      case acc@sil.MagicWand(_,_) => transferMain(states, used,e,allStateAssms)
      case acc@sil.And(e1,e2) => exhaleExt(states, used, e1,allStateAssms) :: exhaleExt(states,used,e2,allStateAssms) :: Nil
      case acc@sil.Implies(e1,e2) => If(expModule.translateExp(e1), exhaleExt(states,used,e2,allStateAssms),Statements.EmptyStmt)
      case acc@sil.CondExp(c,e1,e2) => If(expModule.translateExp(c), exhaleExt(states,used,e1,allStateAssms), exhaleExt(states,used,e2,allStateAssms))
      case _ => exhaleExtExp(states,used,e,allStateAssms)
    }
  }

  def exhaleExtExp(states: List[StateRep], used:StateRep, e: sil.Exp,allStateAssms:Exp):Stmt = {
    if(e.isPure) {
      If(allStateAssms&&used.boolVar,expModule.checkDefinedness(e,mainError),Statements.EmptyStmt) ++
        Assert((allStateAssms&&used.boolVar) ==> expModule.translateExp(e), mainError.dueTo(reasons.AssertionFalse(e)))
    } else {
      sys.error("impure expression not caught in exhaleExt")
    }
  }

  /*
   * Precondition: current state is set to the used state
    */
  def transferMain(states: List[StateRep], used:StateRep, e: sil.Exp, allStateAssms: Exp):Stmt = {
    //store the permission to be transferred into a separate variable
    val permAmount =
      e   match {
        case sil.MagicWand(left, right) => boogieFullPerm
        case p@sil.AccessPredicate(loc, perm) => permModule.translatePerm(perm)
        case _ => sys.error("only transfer of access predicates and magic wands supported")
      }

    val (transferEntity, initStmt)  = setupTransferableEntity(e, transferAmountLocal)
    val initPermVars = (neededLocal := permAmount) ++
      (initNeededLocal := permModule.currentPermission(transferEntity.rcv, transferEntity.loc)+neededLocal)


    val positivePerm = Assert(neededLocal >= RealLit(0), mainError.dueTo(reasons.NegativePermission(e)))

    //val nullCheck =
      //transferEntity match {
      //  case TransferableFieldAccessPred(rcv,loc,_,origAccessPred) =>
      //    Assert((allStateAssms&&used.boolVar) ==> heapModule.checkNonNullReceiver(rcv),mainError.dueTo(reasons.ReceiverNull(origAccessPred.loc)))
      //  case _ => Statements.EmptyStmt
      //}

    val definedness = MaybeCommentBlock("checking if access predicate defined in used state",
      If(allStateAssms&&used.boolVar,expModule.checkDefinedness(e, mainError),Statements.EmptyStmt))

    val transferRest = transferAcc(states,used, transferEntity,allStateAssms)
    val stmt = definedness++ initStmt /*++ nullCheck*/ ++ initPermVars ++  positivePerm ++ transferRest


    MaybeCommentBlock("Transfer of " + e.toString(), stmt)

  }

  /*
   * Precondition: current state is set to the used state
    */
  private def transferAcc(states: List[StateRep], used:StateRep, e: TransferableEntity, allStateAssms: Exp):Stmt = {
    states match {
      case (top :: xs) =>
        //Compute all values needed from top state
        stateModule.replaceState(top.state)
        val isOriginalState: Boolean = xs.isEmpty

        val topHeap = heapModule.currentHeap
        val equateLHS:Option[Exp] = e match {
          case TransferableAccessPred(rcv,loc,_,_) => Some(heapModule.translateLocationAccess(rcv,loc))
          case _ => None
        }

        val definednessTop:Stmt = (boolTransferTop := TrueLit()) ++
          (generateStmtCheck(components flatMap (_.transferValid(e)), boolTransferTop))
        val minStmt = If(neededLocal <= curpermLocal,
          transferAmountLocal := neededLocal, transferAmountLocal := curpermLocal)

        val nofractionsStmt = (transferAmountLocal := RealLit(1.0))

        val curPermTop = permModule.currentPermission(e.rcv, e.loc)
        val removeFromTop = heapModule.beginExhale ++
          (components flatMap (_.transferRemove(e,used.boolVar))) ++
          ( //if original state then don't need to guard assumptions
            if(isOriginalState) {
              heapModule.endExhale ++
                stateModule.assumeGoodState
            } else {
              exchangeAssumesWithBoolean(heapModule.endExhale, top.boolVar) ++
                (top.boolVar := top.boolVar && stateModule.currentGoodState)
              /* exchangeAssumesWithBooleanImpl(heapModule.endExhale, top.boolVar) ++
               Assume(top.boolVar ==> stateModule.currentGoodState) */
            } )

        /*GP: need to formally prove that these two last statements are sound (since they are not
         *explicitily accumulated in the boolean variable */

        //computed all values needed from used state
        stateModule.replaceState(used.state)

        val addToUsed = (components flatMap (_.transferAdd(e,used.boolVar))) ++
          (used.boolVar := used.boolVar&&stateModule.currentGoodState)

        val equateStmt:Stmt = e match {
          case TransferableFieldAccessPred(rcv,loc,_,_) => (used.boolVar := used.boolVar&&(equateLHS.get === heapModule.translateLocationAccess(rcv,loc)))
          case TransferablePredAccessPred(rcv,loc,_,_) =>
            val (tempMask, initTMaskStmt) = permModule.tempInitMask(rcv,loc)
            initTMaskStmt ++
              (used.boolVar := used.boolVar&&heapModule.identicalOnKnownLocations(topHeap,tempMask))
          case _ => Nil
        }

        //transfer from top to used state
        MaybeCommentBlock("transfer code for top state of stack",
          Comment("accumulate constraints which need to be satisfied for transfer to occur") ++ definednessTop ++
            Comment("actual code for the transfer from current state on stack") ++
            If( (allStateAssms&&used.boolVar) && boolTransferTop && neededLocal > boogieNoPerm,
              (curpermLocal := curPermTop) ++
                minStmt ++
                If(transferAmountLocal > boogieNoPerm,
                  (neededLocal := neededLocal - transferAmountLocal) ++
                    addToUsed ++
                    equateStmt ++
                    removeFromTop,

                  Nil),

              Nil
            )
        ) ++ transferAcc(xs,used,e,allStateAssms) //recurse over rest of states
      case Nil =>
        val curPermUsed = permModule.currentPermission(e.rcv,e.loc)
        Assert((allStateAssms&&used.boolVar) ==> (neededLocal === boogieNoPerm && curPermUsed === initNeededLocal),
          e.transferError(mainError))
      /**
       * actually only curPermUsed === permLocal would be sufficient if the transfer is written correctly, since
       * the two conjuncts should be equivalent in theory, but to be safe we ask for the conjunction to hold
       * in case of bugs
       * */
    }
  }

  override def translateApply(app: sil.Apply, error: PartialVerificationError):Stmt = {
    app.exp match {
      case w@sil.MagicWand(left,right) => applyWand(w,error)
      case _ => Nil
    }
  }

  def applyWand(w: sil.MagicWand, error: PartialVerificationError):Stmt = {
    /** we first exhale without havocing heap locations to avoid the incompleteness issue which would otherwise
      * occur when the left and right hand side mention common heap locations.
      */
    CommentBlock("check if wand is held and remove an instance",exhaleModule.exhale((w, error), false)) ++
      stateModule.assumeGoodState ++
      CommentBlock("check if LHS holds and remove permissions ", exhaleModule.exhale((w.left, error), false)) ++
      stateModule.assumeGoodState ++
      CommentBlock("inhale the RHS of the wand",inhaleModule.inhale(w.right)) ++
      heapModule.beginExhale ++ heapModule.endExhale ++
      stateModule.assumeGoodState
    //GP: using beginExhale, endExhale works now, but isn't intuitive, maybe should duplicate code to avoid this breaking
    //in the future when beginExhale and endExhale's implementations are changed
  }

  private def evalArgsAccessPredicate(acc: sil.AccessPredicate, permLocal: Option[sil.LocalVar],error: PartialVerificationError,
                                      b: Option[LocalVar]):
  (Seq[sil.LocalVar],sil.AccessPredicate,Stmt) = {

    val newPerm = permLocal match {
      case Some(p) => p
      case None => acc.perm
    }

    acc match {
      case sil.FieldAccessPredicate(loc,perm) =>
        val SILrcvLocal = mainModule.env.makeUniquelyNamed(sil.LocalVarDecl("rcv", sil.Ref)(loc.rcv.pos,loc.rcv.info)).localVar
        val rcvLocal = mainModule.env.define(SILrcvLocal) //bind Boogie to Silver variable
        val assignStmt = rcvLocal := expModule.translateExp(loc.rcv)
        val newLocation = sil.FieldAccess(SILrcvLocal, loc.field)(acc.pos,acc.info)
        // AS: not convinced this nullCheck is necessary - in any case, the FieldAccessPredicate case for this code seems never to be used.
        //val nullCheck:Stmt = Assert((b.get ==> heapModule.checkNonNullReceiver(newLocation)),error.dueTo(reasons.ReceiverNull(loc)))
        (Seq(SILrcvLocal), sil.FieldAccessPredicate(newLocation,newPerm)(acc.pos,acc.info),assignStmt/*++nullCheck*/)

      case sil.PredicateAccessPredicate(loc,perm) =>
        /* for each argument create a variable and evaluate the argument in the used state */
        val varsAndExprEval: Seq[(sil.LocalVar, Stmt)] = (for (arg <- loc.args) yield {
          val decl = mainModule.env.makeUniquelyNamed(sil.LocalVarDecl("arg", arg.typ)(arg.pos, arg.info))
          val localVar = decl.localVar
          (localVar, mainModule.env.define(localVar) := expModule.translateExp(arg))
        })

        val assignStmt = for ((_,stmt) <- varsAndExprEval) yield {
          stmt
        }

        val localEvalArgs = varsAndExprEval.map( x => x._1)

        /*transform the predicate such that the arguments are now the variables */
        val predAccTransformed = sil.PredicateAccessPredicate(
          sil.PredicateAccess(localEvalArgs, loc.predicateName)(loc.pos, loc.info, loc.errT), newPerm)(acc.pos, acc.info)

        (localEvalArgs, predAccTransformed, assignStmt)

      case mw: sil.MagicWand => sys.error(s"Unexpectedly found magic wand $mw")
    }

  }

  /**
   * @param e expression to be transferred
   * @param permTransfer  expression which denotes the permission amount to be transferred
   * @return a TransferableEntity which can be handled by  all TransferComponents as well as a stmt that needs to be
   *         in the Boogie program before the any translation concerning the TransferableEntity can be used
   */
  private def setupTransferableEntity(e: sil.Exp, permTransfer: Exp):(TransferableEntity,Stmt) = {
    e match {
      case fa@sil.FieldAccessPredicate(loc, perm) =>
        val assignStmt = rcvLocal := expModule.translateExp(loc.rcv)
        val evalLoc = heapModule.translateLocation(loc)
        (TransferableFieldAccessPred(rcvLocal, evalLoc, permTransfer,fa), assignStmt)

      case p@sil.PredicateAccessPredicate(loc, perm) =>
        val localsStmt: Seq[(LocalVar, Stmt)] = (for (arg <- loc.args) yield {
          val v = LocalVar(Identifier(names.createUniqueIdentifier("arg"))(transferNamespace),
            typeModule.translateType(arg.typ))
          (v, v := expModule.translateExp(arg))
        })

        val (locals, assignStmt) = localsStmt.unzip
        val predTransformed = heapModule.translateLocation(p.loc.loc(verifier.program), locals)

        (TransferablePredAccessPred(heapModule.translateNull, predTransformed, permTransfer,p), assignStmt)
      case w:sil.MagicWand =>
        val wandRep = getWandRepresentation(w)
        //GP: maybe should store holes of wand first in local variables
        (TransferableWand(heapModule.translateNull, wandRep, permTransfer, w),Nil)
      case _ => sys.error("Viper expression didn't match any existing case.")
    }
  }

  /*
    *transforms a statement such that it doesn't have any explicit assumptions anymore and all assumptions
    * are accumulated in a single variable, i.e.:
    *
    * Assume x != null
    * Assume y >= 0 is transformed to:
    * b := (b && x!= null); b := (b && y >= 0);
    */
  def exchangeAssumesWithBoolean(stmt: Stmt,boolVar: LocalVar):Stmt = {
    stmt match {
      case Assume(exp) =>
        boolVar := (boolVar && exp)
      case Seqn(statements) =>
        Seqn(statements.map(s => exchangeAssumesWithBoolean(s, boolVar)))
      case If(c,thn,els) =>
        If(c,exchangeAssumesWithBoolean(thn,boolVar),exchangeAssumesWithBoolean(els,boolVar))
      case NondetIf(thn,els) =>
        NondetIf(exchangeAssumesWithBoolean(thn,boolVar))
      case CommentBlock(comment,s) =>
        CommentBlock(comment, exchangeAssumesWithBoolean(s,boolVar))
      case s => s
    }
  }

  def exchangeAssumesWithBooleanImpl(stmt: Stmt,boolVar: LocalVar):Stmt = {
    stmt match {
      case Assume(exp) =>
        Assume(boolVar ==> exp)
      case Seqn(statements) =>
        Seqn(statements.map(s => exchangeAssumesWithBoolean(s, boolVar)))
      case If(c,thn,els) =>
        If(c,exchangeAssumesWithBoolean(thn,boolVar),exchangeAssumesWithBoolean(els,boolVar))
      case NondetIf(thn,els) =>
        NondetIf(exchangeAssumesWithBoolean(thn,boolVar))
      case CommentBlock(comment,s) =>
        CommentBlock(comment, exchangeAssumesWithBoolean(s,boolVar))
      case s => s
    }
  }

  /*
   * Let the argument be a sequence [(s1,e1),(s2,e2)].
   * Then the function returns:
   * (s1; b := b&&e1; s2; b := b&&e2)
   */
  def generateStmtCheck(x: Seq[(Stmt,Exp)], boolVar:LocalVar):Stmt = {
    (x map (y => y._1 ++ (boolVar := boolVar&&y._2))).flatten
  }

  /*
   *this class is used to group the local boogie variables used for the transfer which are potentially different
   * for each transfer (in contrast to "neededLocal" which ist declared as a constant)
   */
  case class TransferBoogieVars(transferAmount: LocalVar, boolVar: LocalVar)

  /*
   * is used to store relevant blocks needed to start an exec or package
   */
  case class PackageSetup(hypState: StateRep, usedState: StateRep, initStmt: Stmt)

  /*
   * is used to store relevant blocks needed to use a newly created state
   */
  case class StateSetup(usedState: StateRep, initStmt: Stmt)

  case class StateRep(state: StateSnapshot, boolVar: LocalVar)


}

