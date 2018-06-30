package viper.carbon.modules.impls


import org.scalatest.GivenWhenThen
import viper.carbon.modules._
import viper.carbon.verifier.Verifier
import viper.carbon.boogie._
import viper.carbon.boogie.Implicits._
import viper.carbon.modules.components.{DefinednessComponent, StmtComponent}
import viper.silver.ast.utility.Expressions
import viper.silver.ast.{FullPerm, MagicWand, MagicWandStructure, PredicateAccessPredicate}
import viper.silver.verifier.{PartialVerificationError, errors, reasons}
import viper.silver.{ast => sil}

import scala.collection.mutable.ListBuffer


/**
 * Created by Gaurav on 06.03.2015.
 */


class
DefaultWandModule(val verifier: Verifier) extends WandModule with StmtComponent with DefinednessComponent{
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


  //use this to generate unique names for states
  private val names = new BoogieNameGenerator()


  // states variables
  var OPS: StateRep = null
  tempCurState = null
  wandId = 0

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

  override def translatePackage(p: sil.Package, error: PartialVerificationError, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false):Stmt = {
    val proofScript = p.proofScript
    p match {
      case pa@sil.Package(wand, proof) =>
        wand match {
          case w@sil.MagicWand(left,right) =>

            val addWand = inhaleModule.inhale(w, statesStack, inWand)
            val currentState = stateModule.state

            val oldOps = OPS

            val PackageSetup(opsState, usedState, initStmt) = packageInit(wand, None, error)
            val curStateBool = LocalVar(Identifier(names.createUniqueIdentifier("boolCur"))(transferNamespace),Bool)

            val newStack =
              if(inWand)
                statesStack.asInstanceOf[List[StateRep]]
              else
                StateRep(currentState, curStateBool) :: Nil


            val locals = proofScript.scopedDecls.collect {case l: sil.LocalVarDecl => l}
            locals map (v => mainModule.env.define(v.localVar)) // add local variables to environment

            val stmt = initStmt++(curStateBool := TrueLit()) ++
              MaybeCommentBlock("Assumptions about local variables", locals map (a => mainModule.allAssumptionsAboutValue(a.typ, mainModule.translateLocalVarDecl(a), true))) ++
              execBody(newStack, opsState, proofScript.ss , right, opsState.boolVar && allStateAssms, error)

            locals map (v => mainModule.env.undefine(v.localVar)) // remove local variables from environment
            OPS = oldOps

            stateModule.replaceState(currentState)
            lhsStack = lhsStack.dropRight(1)
            wandId -= 1
            stmt ++ addWand

          case _ => sys.error("Package only defined for wands.")
        }
    }
  }

  def execBody(states: List[StateRep], ops: StateRep, proofScript: Seq[sil.Stmt], right: sil.Exp, allStateAssms: Exp, error: PartialVerificationError):Stmt = {
    (proofScript map(s => translateInWandStatement(states, ops, s, allStateAssms)))++
    exec(states,ops, right, allStateAssms, error)
  }

  def translateInWandStatement(states: List[StateRep], ops: StateRep, s: sil.Stmt, allStateAssms: Exp): Stmt =
  {
    UNIONState = OPS
    val initStmt: Stmt = Statements.EmptyStmt
    stateModule.replaceState(OPS.state)
    initStmt ++ If(allStateAssms, stmtModule.translateStmt(s, ops::states, allStateAssms , true), Statements.EmptyStmt)
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
  def exec(states: List[StateRep], ops: StateRep, e:sil.Exp, allStateAssms: Exp, mainError: PartialVerificationError):Stmt = {
    e match {
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
          exec(states,ops,instantiatedExp,allStateAssms, mainError)

        mainModule.env.undefine(v.localVar)

        stmt
      case _ =>
        //no ghost operation
        UNIONState = OPS
        val StateSetup(usedState, initStmt) = createAndSetState(None)
        tempCurState = usedState
        Comment("Translating exec of non-ghost operation" + e.toString()) ++
        initStmt ++  exhaleExt(ops :: states, usedState,e,ops.boolVar&&allStateAssms, RHS = true, mainError)
    }
  }

  var lhsID = 0
  var lhsStack: List[Int] = Nil
  /**
   * @param wand wand to be packaged
   * @param boolVar boolean variable to which the newly generated boolean variable associated with the package should
   *                be set to in the beginning
   * @return structure that contains all the necessary blocks to initiate a package
   *
   * Postcondition: state is set to the "Used" state generated in the function
   */
  private def packageInit(wand:sil.MagicWand, boolVar: Option[LocalVar], mainError: PartialVerificationError):PackageSetup = {
    val StateSetup(usedState, initStmt) = createAndSetState(boolVar, "Used", false).asInstanceOf[StateSetup]

    //inhale left hand side to initialize hypothetical state
    val hypName = names.createUniqueIdentifier("Ops")
    val StateSetup(hypState,hypStmt) = createAndSetState(None,"Ops")
    OPS = hypState
    UNIONState = OPS
    wandId += 1
    val inhaleLeft = MaybeComment("Inhaling left hand side of current wand into hypothetical state",
      exchangeAssumesWithBoolean(expModule.checkDefinednessOfSpecAndInhale(wand.left, mainError, hypState::Nil, true), hypState.boolVar))
    // Vs     val inhaleLeft = MaybeComment("Inhaling left hand side of current wand into hypothetical state",
//          If(hypState.boolVar, expModule.checkDefinednessOfSpecAndInhale(wand.left, mainError), Statements.EmptyStmt))

    val defineLHS = stmtModule.translateStmt(sil.Label("lhs"+lhsID, Nil)(wand.pos, wand.info), hypState::Nil, hypState.boolVar, true)
    lhsStack = lhsStack:+lhsID
    lhsID += 1

    stateModule.replaceState(usedState.state)

    PackageSetup(hypState, usedState, (trueBool := TrueLit()) ++ hypStmt ++ initStmt ++ inhaleLeft ++ defineLHS)
  }

  override def createAndSetState(initBool:Option[Exp],usedString:String = "Used",setToNew:Boolean=true,
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

//    val (usedStmt, currentState) = stateModule.freshTempState(usedName,init)
    val (usedStmt, currentState) = stateModule.freshEmptyState(usedName,init)
    val usedState = stateModule.state

    val goodState = exchangeAssumesWithBoolean(stateModule.assumeGoodState, b)

    /**DEFINE STATES END **/
    if(!setToNew) {
      stateModule.replaceState(currentState)
    }

    StateSetup(StateRep(usedState,b),usedStmt++boolStmt++goodState)
  }


//create a state Result which is the "sum" of the current  and Other state
override def createAndSetSumState(stateOtherO: Any ,boolOther:Exp,boolCur:Exp):StateSetup = {
  // get heap and mask from other state
  val stateOther = stateOtherO.asInstanceOf[StateSnapshot]
  val currentState = stateModule.state
  stateModule.replaceState(stateOther)
  val heapOther = heapModule.currentHeap
  val maskOther = permModule.currentMask
  stateModule.replaceState(currentState)

  createAndSetSumState(heapOther, maskOther, boolOther, boolCur)
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

override def exhaleExt(statesObj: List[Any], usedObj:Any, e: sil.Exp, allStateAssms: Exp, RHS: Boolean = false, error: PartialVerificationError, havocHeap: Boolean):Stmt = {
  Comment("exhale_ext of " + e.toString())
  var states = statesObj.asInstanceOf[List[StateRep]]
  var used = usedObj.asInstanceOf[StateRep]
  e match {
    case acc@sil.AccessPredicate(_,_) => transferMain(states,used, e, allStateAssms, error, havocHeap)
    case acc@sil.MagicWand(_,_) => transferMain(states, used,e,allStateAssms, error, havocHeap)
    case acc@sil.And(e1,e2) =>
      exhaleExt(states, used, e1,allStateAssms, RHS, error, havocHeap) :: exhaleExt(states,used,e2,allStateAssms, RHS, error, havocHeap) :: Nil
    case acc@sil.Implies(e1,e2) =>
      If(allStateAssms,
        If(expModule.translateExpInWand(e1), exhaleExt(states,used,e2,allStateAssms, RHS, error, havocHeap),Statements.EmptyStmt),
        Statements.EmptyStmt)
    case acc@sil.CondExp(c,e1,e2) =>
      If(allStateAssms,
        If(expModule.translateExpInWand(c), exhaleExt(states,used,e1,allStateAssms, RHS, error, havocHeap), exhaleExt(states,used,e2,allStateAssms, RHS, error, havocHeap)),
        Statements.EmptyStmt)
    case _ => exhaleExtExp(states,used,e,allStateAssms, RHS, error)
  }
}

def exhaleExtExp(states: List[StateRep], used:StateRep, e: sil.Exp,allStateAssms:Exp, RHS: Boolean = false, mainError: PartialVerificationError):Stmt = {
  if(e.isPure) {
    // AG: Should RHS be treated differently? For example to be checked in Used state only without Ops?
    If(allStateAssms&&used.boolVar,expModule.checkDefinedness(e,mainError, inWand = true),Statements.EmptyStmt) ++
      Assert((allStateAssms&&used.boolVar) ==> expModule.translateExpInWand(e), mainError.dueTo(reasons.AssertionFalse(e)))

  } else {
    sys.error("impure expression not caught in exhaleExt")
  }
}

/*
 * Precondition: current state is set to the used state
  */
def transferMain(states: List[StateRep], used:StateRep, e: sil.Exp, allStateAssms: Exp, mainError: PartialVerificationError, havocHeap: Boolean = true):Stmt = {
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


  val definedness =
    MaybeCommentBlock("checking if access predicate defined in used state",
    If(allStateAssms&&used.boolVar,expModule.checkDefinedness(e, mainError, inWand = true),Statements.EmptyStmt))

  val transferRest = transferAcc(states,used, transferEntity,allStateAssms, mainError, havocHeap)
  val stmt = definedness++ initStmt /*++ nullCheck*/ ++ initPermVars ++  positivePerm ++ transferRest

  val unionStmt = updateUnion()

  MaybeCommentBlock("Transfer of " + e.toString(), stmt ++ unionStmt)

}

/*
 * Precondition: current state is set to the used state
  */
private def transferAcc(states: List[StateRep], used:StateRep, e: TransferableEntity, allStateAssms: Exp, mainError: PartialVerificationError, havocHeap: Boolean = true):Stmt = {
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
          } else if(top != OPS || havocHeap){
              exchangeAssumesWithBoolean(heapModule.endExhale, top.boolVar) ++
              (top.boolVar := top.boolVar && stateModule.currentGoodState)
            /* exchangeAssumesWithBooleanImpl(heapModule.endExhale, top.boolVar) ++
             Assume(top.boolVar ==> stateModule.currentGoodState) */
          }else
            top.boolVar := top.boolVar && stateModule.currentGoodState)

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
      ) ++ transferAcc(xs,used,e,allStateAssms, mainError, havocHeap) //recurse over rest of states
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

override def translateApply(app: sil.Apply, error: PartialVerificationError, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false):Stmt = {
  app.exp match {
    case w@sil.MagicWand(left,right) => applyWand(w,error, statesStack, allStateAssms, inWand)
    case _ => Nil
  }
}

def applyWand(w: sil.MagicWand, error: PartialVerificationError, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false):Stmt = {
  /** we first exhale without havocing heap locations to avoid the incompleteness issue which would otherwise
    * occur when the left and right hand side mention common heap locations.
    */
  val defineLHS = stmtModule.translateStmt(sil.Label("lhs"+wandModule.getLhsId(), Nil)(w.pos, w.info))
  wandModule.pushLhsStack(wandModule.getLhsId())
  wandModule.incLhsId()

  val ret = CommentBlock("check if wand is held and remove an instance",exhaleModule.exhale((w, error), false, inWand = inWand, statesStack = statesStack)) ++
    (if(inWand) exchangeAssumesWithBoolean(stateModule.assumeGoodState, OPS.boolVar) else stateModule.assumeGoodState) ++
    CommentBlock("check if LHS holds and remove permissions ", exhaleModule.exhale((w.left, error), false, inWand = inWand, statesStack = statesStack)) ++
    (if(inWand) exchangeAssumesWithBoolean(stateModule.assumeGoodState, OPS.boolVar) else stateModule.assumeGoodState) ++
    CommentBlock("inhale the RHS of the wand",inhaleModule.inhale(w.right, statesStack = statesStack, inWand = inWand)) ++
    heapModule.beginExhale ++ heapModule.endExhale ++
    (if(inWand) exchangeAssumesWithBoolean(stateModule.assumeGoodState, OPS.boolVar) else stateModule.assumeGoodState)
  //GP: using beginExhale, endExhale works now, but isn't intuitive, maybe should duplicate code to avoid this breaking
  //in the future when beginExhale and endExhale's implementations are changed
  popLhsStack()
  ret
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
      val assignStmt = rcvLocal := expModule.translateExpInWand(loc.rcv)
      val evalLoc = heapModule.translateLocation(loc)
      (TransferableFieldAccessPred(rcvLocal, evalLoc, permTransfer,fa), assignStmt)

    case p@sil.PredicateAccessPredicate(loc, perm) =>
      val localsStmt: Seq[(LocalVar, Stmt)] = (for (arg <- loc.args) yield {
        val v = LocalVar(Identifier(names.createUniqueIdentifier("arg"))(transferNamespace),
          typeModule.translateType(arg.typ))
        (v, v := expModule.translateExpInWand(arg))
      })

      val (locals, assignStmt) = localsStmt.unzip
      val predTransformed = heapModule.translateLocation(p.loc.loc(verifier.program), locals)

      (TransferablePredAccessPred(heapModule.translateNull, predTransformed, permTransfer,p), assignStmt)
    case w:sil.MagicWand =>
      val wandRep = getWandRepresentation(w)
      //GP: maybe should store holes of wand first in local variables
      (TransferableWand(heapModule.translateNull, wandRep, permTransfer, w),Nil)
  }
}

override def exchangeAssumesWithBoolean(stmt: Stmt,boolVar: LocalVar):Stmt = {
  stmt match {
    case Assume(exp) =>
      boolVar := (boolVar && viper.carbon.boogie.PrettyPrinter.quantifyOverFreeTypeVars(exp))
    case Seqn(statements) =>
      Seqn(statements.map(s => exchangeAssumesWithBoolean(s, boolVar)))
    case If(c, thn, els) =>
      If(c, exchangeAssumesWithBoolean(thn, boolVar), exchangeAssumesWithBoolean(els, boolVar))
    case NondetIf(thn, els) =>
      NondetIf(exchangeAssumesWithBoolean(thn, boolVar))
    case CommentBlock(comment, s) =>
      CommentBlock(comment, exchangeAssumesWithBoolean(s, boolVar))
    case s => s
  }
}

  /**
    * Transforms all asserts and if conditions in the statement as following:
    * Assert e is transformed to: Assert (boolVar => e)
    * if(c) {...} else {...} is transformed to: if(boolVar){ if(c) {...} else {...} }
    * where boolVar represents the boolean expression carrying assumptions about some states.
    */
  def modifyAssert(stmt: Stmt,boolVar: LocalVar):Stmt = {
    stmt match {
      case Assert(exp, error) => Assert(boolVar ==> exp, error)
      case Seqn(statements) =>
        Seqn(statements.map(s => modifyAssert(s, boolVar)))
      case If(c,thn,els) =>
        If(boolVar, If(c,modifyAssert(thn,boolVar),modifyAssert(els,boolVar)), Statements.EmptyStmt)
      case NondetIf(thn,els) =>
        NondetIf(modifyAssert(thn,boolVar))
      case CommentBlock(comment,s) =>
        CommentBlock(comment, modifyAssert(s,boolVar))
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

  override def updateUnion(): Stmt = {
    val oldCurState = stateModule.state
    stateModule.replaceState(tempCurState.asInstanceOf[StateRep].state)
    val StateSetup(resultState, unionStatement) = createAndSetSumState(OPS.state, OPS.boolVar, tempCurState.asInstanceOf[StateRep].boolVar)
    UNIONState = resultState
    stateModule.replaceState(oldCurState)
    unionStatement ++ (OPS.boolVar := OPS.boolVar && resultState.boolVar)
  }

  /**
    * Wraps all statements inside package statement inside If condition.
    */
  override  def handleStmt(s: sil.Stmt, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false): (Seqn => Seqn) = {
    if(wandModule.wandId > 0)
      stmt => If(allStateAssms, modifyAssert(stmt, OPS.boolVar), Statements.EmptyStmt)::Nil
    else
      stmt => stmt
  }

  override def prepareStmt(): Unit ={
    UNIONState = OPS
    stateModule.replaceState(OPS.state)
  }

  override def getActiveLhs(): Int = {
    lhsStack.last
  }

  override def getLhsId():Int ={
    lhsID
  }

  override def pushLhsStack(lhsNum: Int): Unit ={
    lhsStack = lhsStack:+lhsNum
  }

  override def popLhsStack(): Unit ={
    lhsStack = lhsStack.dropRight(1)
  }

  override def incLhsId():Unit ={
    lhsID = lhsID+1
  }

  override def start() {
    stmtModule.register(this, before = Seq(verifier.heapModule,verifier.permModule, verifier.stmtModule)) // checks for field assignment should be made before the assignment itself
    expModule.register(this)
  }


  private var tmpStateId = -1

  /**
    * Checking definedness for applying statement
    */
  override def partialCheckDefinedness(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean): (() => Stmt, () => Stmt) = {
    e match {
      case a@sil.Applying(wand, exp) =>
        tmpStateId += 1
        val tmpStateName = if (tmpStateId == 0) "Applying" else s"Applying$tmpStateId"
        val (stmt, state) = stateModule.freshTempState(tmpStateName)
        def before() = {
          stmt ++ applyWand(wand, error, inWand = false)
        }
        def after() = {
          tmpStateId -= 1
          stateModule.replaceState(state)
          Nil
        }
        (before, after)
      case _ => (() => simplePartialCheckDefinedness(e, error, makeChecks), () => Nil)
    }
  }


  var trueBool = LocalVar(Identifier(names.createUniqueIdentifier("boolTrue"))(transferNamespace),Bool)

  override def getCurOpsBoolvar(): LocalVar = {
    if(wandId > 0)
      OPS.boolVar
    else
      trueBool
  }

  override def getOps(): StateRep = {
    OPS
  }

  override def initTrueBool(): Stmt = {
    (trueBool := TrueLit())
  }
}
