package viper.carbon.modules.impls


import org.scalatest.GivenWhenThen
import viper.carbon.modules.WandModule
import viper.carbon.modules.components.{TransferComponent, DefinednessComponent}
import viper.carbon.verifier.Verifier
import viper.carbon.boogie._
import viper.carbon.boogie.Implicits._
import viper.silver.ast.MagicWand

import viper.silver.verifier.{errors, reasons, PartialVerificationError}
import viper.silver.{ast => sil}

import scala.collection.mutable.ListBuffer


/**
 * Created by Gaurav on 06.03.2015.
 */


class DefaultWandModule(val verifier: Verifier) extends WandModule {
  import verifier._
  import stateModule._
  import permModule._

  val transferNamespace = verifier.freshNamespace("transfer")
  val wandNamespace = verifier.freshNamespace("wands")
//wands stored
  type WandShape = Func
  var wandToShapes: java.util.HashMap[sil.MagicWand, WandShape] = new java.util.HashMap[sil.MagicWand, WandShape]
  var wandShapes: ListBuffer[(sil.MagicWand,WandShape, Type)] = new ListBuffer[(sil.MagicWand, WandShape,Type)]();
/** CONSTANTS FOR TRANSFER START**/

/* denotes amount of permission to add/remove during a specific transfer,
 * this is inserted as permission into the initial AccessPredicate such that existing interfaces can be used
 * and the transfer can be kept general
 * */
  val SILtempLocalDecl: sil.LocalVarDecl = sil.LocalVarDecl("takeTransfer", sil.Perm)(sil.NoPosition,sil.NoInfo)

  /*stores amount of permission still needed during transfer*/
  val neededLocal: LocalVar = LocalVar(Identifier("neededTransfer")(transferNamespace),permType)

  /*stores initial amount of permission needed during transfer*/
  val initNeededLocal = LocalVar(Identifier("initNeededTransfer")(transferNamespace), permType)

  /*used to store the current permission of the top state of the stack during transfer*/
  val curpermLocal = LocalVar(Identifier("maskTransfer")(transferNamespace), permType)

/*denotes the receiver evaluated in the Used state, this is inserted as receiver to FieldAccessPredicates such that
* existing interfaces can be reused and the transfer can be kept general */
  val SILrcvLocalDecl: sil.LocalVarDecl = sil.LocalVarDecl("rcvTransfer", sil.Ref)(sil.NoPosition,sil.NoInfo)

/* boolean variable which is used to accumulate assertions concerning the validity of a transfer*/
  val boolTransferTop = LocalVar(Identifier("accVar2")(transferNamespace), Bool)

/** CONSTANTS FOR TRANSFER END**/

  /* Gaurav (03.04.15): this seems nicer as an end result in the Boogie program but null for pos,info params is
   * not really nice
   *   val boogieNoPerm:Exp = permModule.translatePerm(sil.NoPerm()(null,null))
  */
  val boogieNoPerm:Exp = RealLit(0)

  var mainError: PartialVerificationError = null


  //use this to generate unique names for states
  private val names = new BoogieNameGenerator()


  def name = "Wand Module"

  override def initialize() {
    register(this)
  }

  override def preamble = {
    (for ((wand,fun@Func(name,args,typ),wandType) <- wandShapes.result()) yield {
      val vars = args.map(decl => decl.l)
      val f0 = FuncApp(name,vars,typ)
      val typeDecl:Seq[TypeDecl] = wandType match {
        case named: NamedType => TypeDecl(named)
        case _ => Nil
      }
      typeDecl ++
      fun ++
      Axiom(MaybeForall(args, Trigger(f0),heapModule.isWandField(f0))) ++
      Axiom(MaybeForall(args, Trigger(f0),heapModule.isPredicateField(f0).not))
    }).flatten
  }

  override def transferRemove(e:sil.Exp, cond:Exp): Stmt = {
    Nil
  }

  def transferAdd(e:sil.Exp, cond: Exp): Stmt = {
    Nil
  }

  def transferValid(e:sil.Exp):Seq[(Stmt,Exp)] = {
    Nil
  }

  /*
   * method returns the boogie predicate which corresponds to the magic wand shape of the given wand
   * if the shape hasn't yet been recorded yet then it will be stored
   */
  def getWandRepresentation(wand: sil.MagicWand):Exp = {
    //first check if the shape to this wand has already been computed earlier
    val maybeShape = wandToShapes.get(wand)

    //get all the expressions which form the "holes" of the shape,
    val arguments = wand.subexpressionsToEvaluate(mainModule.verifier.program)

    val shape:WandShape =
      if (maybeShape != null) {
        maybeShape
      } else {
        //need to compute shape of wand
        val ghostFreeWand = wand.withoutGhostOperations
        //check if shape of wand corresponds to an already computed shape
        val findShape = wandShapes.find(wand_pred =>
          ghostFreeWand.structurallyMatches(wand_pred._1, mainModule.verifier.program))
        val newShape = findShape match {
          case None =>
            //new shape was found
            val wandName = names.createUniqueIdentifier("wand")
            val wandType = heapModule.wandFieldType(wandName)

            //for each expression which is a "hole" in the shape we create a local variable declaration which will be used
            //for the function corresponding to the wand shape
            var i = 0
            val argsWand = (for (arg <- arguments) yield {
              i = i + 1
              LocalVarDecl(Identifier("arg" + i)(wandNamespace), typeModule.translateType(arg.typ), None)
            })
            val wandFun = Func(Identifier(wandName)(wandNamespace), argsWand, wandType)
            val res = (ghostFreeWand, wandFun, heapModule.wandBasicType(wandName))
            //add new shape
            wandShapes += res
            wandFun
          case Some((_, wandFun, _)) =>
            //computed shape already corresponded to an earlier computed shape
            wandFun
        }
        wandToShapes.put(wand, newShape)
        newShape
      }

    shape match {
      case Func(name, args,typ) => FuncApp(name, arguments.map(arg => expModule.translateExp(arg)), typ)
    }
  }

  override def translatePackage(p: sil.Package,error: PartialVerificationError):Stmt = {
    p match {
      case pa@sil.Package(wand) =>
        wand match {
          case w@sil.MagicWand(left,right) =>
            mainError = error //set the default error to be used by all operations

            val addWand = inhaleModule.inhale(w)
            val currentState = stateModule.getCopyState

            val PackageSetup(hypState, usedState, initStmt, boolVar) = packageInit(wand, None)

            val stmt = initStmt ++ exec(hypState :: currentState :: Nil, usedState, right, boolVar)

            stateModule.restoreState(currentState)

            stmt ++ addWand

          //TODO: add wand to current state
          case _ => sys.error("Package only defined for wands.")
        }
    }
  }

  def exec(states: List[StateSnapshot], ops: StateSnapshot, e:sil.Exp, b: LocalVar):Stmt = {
    e match {
      case fold@sil.Folding(acc,body) =>
        val opsMask = permModule.currentMask
        val opsHeap = heapModule.currentHeap

        val UsedStateSetup(usedState, initStmt, boolUsed) = createAndSetState(Some(b))
        Comment("Translating " + fold.toString()) ++ initStmt ++
          { //get permissions for unfold and then unfold
             val sil.PredicateAccessPredicate(loc,perm) = acc

            val (argsLocal, accTransformed, assignStmt) = evalArgsAccessPredicate(acc, None,mainError,None)
            val predAccTransformed = accTransformed match {
              case pap@sil.PredicateAccessPredicate(_,_) => pap
              case _ =>  sys.error("evalArgsAccessPredicate returned FieldAccessPredicate for input PredicateAccessPredicate")
            }

            stateModule.restoreState(usedState)

            val permForBody = exhaleExt(ops :: states, usedState, loc.predicateBody(verifier.program).get, boolUsed)
            val foldStmt = If(boolUsed, funcPredModule.translateFold(sil.Fold(predAccTransformed)(fold.pos, fold.info)),
              Statements.EmptyStmt)

            argsLocal.foreach(localVar => mainModule.env.undefine(localVar))

            CommentBlock("Retrieving permissions to execute fold and then folding the predicate",
              assignStmt ++ permForBody ++ foldStmt)
          } ++ {
          //exec in sum state
          val usedHeap = heapModule.currentHeap
          val usedMask = permModule.currentMask

          /*create a state Result which is the "sum" of the ops and used states, i.e.:
             *1) at each heap location o.f the permission of the Result state is the sum of the permissions
             * for o.f in the ops and Used state
             * 2) if ops has some positive nonzero amount of permission for heap location o.f then the heap values for
             * o.f in ops and Result are the same
             * 3) point 2) also holds for the used state in place of the ops state
             *
             * Note: the boolean is the conjunction of the booleans of ops and used (since all facts of each
             * state is transferred)
              */
          val UsedStateSetup(resultState, initStmtResult, boolRes) =
            createAndSetState(Some(b && boolUsed), "Result", true, false)

          val sumStates = (boolRes := boolRes && permModule.sumMask(opsMask, usedMask))
          val equateKnownValues = (boolRes := boolRes && heapModule.identicalOnKnownLocations(opsHeap, opsMask) &&
            heapModule.identicalOnKnownLocations(usedHeap, usedMask))
          val goodState = exchangeAssumesWithBoolean(stateModule.assumeGoodState, boolRes)

          CommentBlock("Creating state which is the sum of the two previously built up states",
            initStmtResult ++ sumStates ++ equateKnownValues ++ goodState) ++
            Comment("Translating exec of body of fold") ++
            exec(states, resultState, body, boolRes)
        }
      case unfold@sil.Unfolding(acc,body) =>
        val opsMask = permModule.currentMask
        val opsHeap = heapModule.currentHeap

        val UsedStateSetup(usedState, initStmt, boolUsed) = createAndSetState(Some(b))
        Comment("Translating " + unfold.toString()) ++ initStmt ++
          { //get permissions for unfold and then unfold
          val sil.PredicateAccessPredicate(loc,perm) = acc

            val (argsLocal, accTransformed, assignStmt) = evalArgsAccessPredicate(acc, None,mainError,None)
            val predAccTransformed = accTransformed match {
              case pap@sil.PredicateAccessPredicate(_,_) => pap
              case _ =>  sys.error("evalArgsAccessPredicate returned FieldAccessPredicate for input PredicateAccessPredicate")
            }

            stateModule.restoreState(usedState)

            val permForPred = exhaleExt(ops :: states, usedState, accTransformed, boolUsed)
            val unfoldStmt = CommentBlock("unfolding " + acc.toString() ,
              If(boolUsed, funcPredModule.translateUnfold(sil.Unfold(predAccTransformed)(unfold.pos, unfold.info)),
              Statements.EmptyStmt) )

            argsLocal.foreach(localVar => mainModule.env.undefine(localVar))
            CommentBlock("Retrieving permissions to execute unfold and then unfolding the predicate",
            assignStmt ++ permForPred ++ unfoldStmt)
          } ++ {
          //exec in sum state
          val usedHeap = heapModule.currentHeap
          val usedMask = permModule.currentMask

          /*create a state Result which is the "sum" of the ops and used states, i.e.:
           *1) at each heap location o.f the permission of the Result state is the sum of the permissions
           * for o.f in the ops and Used state
           * 2) if ops has some positive nonzero amount of permission for heap location o.f then the heap values for
           * o.f in ops and Result are the same
           * 3) point 2) also holds for the used state in place of the ops state
           *
           * Note: the boolean is the conjunction of the booleans of ops and used (since all facts of each
           * state is transferred)
            */
          val UsedStateSetup(resultState, initStmtResult, boolRes) =
            createAndSetState(Some(b && boolUsed), "Result", true, false)

          val sumStates = (boolRes := boolRes && permModule.sumMask(opsMask, usedMask))
          val equateKnownValues = (boolRes := boolRes && heapModule.identicalOnKnownLocations(opsHeap, opsMask) &&
            heapModule.identicalOnKnownLocations(usedHeap, usedMask))
          val goodState = exchangeAssumesWithBoolean(stateModule.assumeGoodState, boolRes)
          CommentBlock("Creating state which is the sum of the two previously built up states",
          initStmtResult ++ sumStates ++ equateKnownValues ++ goodState) ++
          exec(states, resultState, body, boolRes)
        }
      case sil.Applying(wand, body) =>
        sys.error("exec: applying not yet supported")
      case p@sil.Packaging(wand,body) =>
        val addWand = inhaleModule.inhale(wand)

        val PackageSetup(hypState, usedState, initStmt, b_new) = packageInit(wand, Some(b))

        val execInnerWand = exec(hypState :: ops :: states, usedState, wand.right, b_new)

        val packaging =  MaybeCommentBlock("Code for the packaging of wand" + wand.toString() +" in" + p.toString(),
          initStmt ++ execInnerWand)

        stateModule.restoreState(ops)

        MaybeCommentBlock("Translating " + p.toString(),
          packaging ++ addWand ++ MaybeCommentBlock("Code for body " + body.toString() + " of " + p.toString(), exec(states,ops,body,b)) )

      case _ =>
        //no ghost operation
        val UsedStateSetup(usedState, initStmt, boolVar) = createAndSetState(Some(b))
        Comment("Translating exec of non-ghost operation" + e.toString())
        initStmt ++ exhaleExt(ops :: states, usedState,e,b)
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
    val UsedStateSetup(usedState, initStmt, b) = createAndSetState(boolVar, "Used", false)

    //inhale left hand side to initialize hypothetical state
    val hypName = names.createUniqueIdentifier("Hyp")
    val (hypStmt, hypState) = stateModule.freshEmptyState(hypName, true)
    stateModule.restoreState(hypState)

    val inhaleLeft = MaybeComment("Inhaling left hand side of current wand into hypothetical state",
      If(b, expModule.checkDefinednessOfSpecAndInhale(wand.left, mainError), Statements.EmptyStmt))

    stateModule.restoreState(usedState)

    PackageSetup(hypState, usedState, hypStmt ++ initStmt ++ inhaleLeft, b)
  }


  /**
   *
   * @param initBool boolean value to which the newly generated boolean variable should be initialized to
   * @param usedString string to incorporate into unique name for string
   * @param setToNew the state is set to the generated state iff this is set to true
   * @param init if this is set to true then the stmt in UsedStateSetup will initialize the states (for example
   *             masks to ZeroMask), otherwise the states contain no information
   * @return  Structure which can be used at the beginning of many operations involved in the package
   */
  private def createAndSetState(initBool:Option[Exp],usedString:String = "Used",setToNew:Boolean=true,
                                init:Boolean=true):UsedStateSetup = {
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
    val (usedStmt, usedState) = stateModule.freshEmptyState(usedName,init)

    /**DEFINE STATES END **/
    if(setToNew) {
      stateModule.restoreState(usedState)
    }

    UsedStateSetup(usedState,usedStmt++boolStmt, b)
  }

  /*generates code that transfers permissions from states to used such that e can be satisfied
    * Precondition: current state is set to the used state
    * */
   def exhaleExt(states: List[StateSnapshot], used:StateSnapshot, e: sil.Exp, b:LocalVar):Stmt = {
    Comment("exhale_ext of " + e.toString())
    e match {
      case acc@sil.AccessPredicate(_,_) => transferMain(states,used, e, b) //transfer(states, used, acc)
      case acc@sil.MagicWand(_,_) => sys.error("exhaleExtConnective: Magic Wands not yet supported ")
      case acc@sil.And(e1,e2) => exhaleExt(states, used, e1,b) :: exhaleExt(states,used,e2,b) :: Nil
      case acc@sil.Implies(e1,e2) => If(expModule.translateExp(e1), exhaleExt(states,used,e2,b),Statements.EmptyStmt)
      case acc@sil.CondExp(c,e1,e2) => If(expModule.translateExp(c), exhaleExt(states,used,e1,b), exhaleExt(states,used,e2,b))
      case _ => exhaleExtExp(states,used,e,b)
    }
  }

  def exhaleExtExp(states: List[StateSnapshot], used:StateSnapshot, e: sil.Exp, b:LocalVar):Stmt = {
    if(e.isPure) {
      If(b,expModule.checkDefinedness(e,mainError),Statements.EmptyStmt) ++
      Assert(b ==> expModule.translateExp(e), mainError.dueTo(reasons.AssertionFalse(e)))
    } else {
      sys.error("impure expression not caught in exhaleExt")
    }
  }

 /*
  * Precondition: current state is set to the used state
   */
  def transferMain(states: List[StateSnapshot], used:StateSnapshot, e: sil.Exp, b: LocalVar):Stmt = {
    e match {
      case sil.MagicWand(left,right) => sys.error("still need to implement this")
      case p@sil.AccessPredicate(loc,perm)  =>
        //initialize Boogie local variables used during the transfer
        val SILtempLocal = mainModule.env.makeUniquelyNamed(SILtempLocalDecl).localVar
        val tempLocal = mainModule.env.define(SILtempLocal) //bind Boogie to Silver variable

        val (argLocals,accTransformed, assignStmt) : (Seq[sil.LocalVar],sil.AccessPredicate, Stmt) =
          evalArgsAccessPredicate(p,Some(SILtempLocal),mainError,Some(b))

        val permAmount = permModule.translatePerm(perm) //store the permission to be transferred into a separate variable
        val positivePerm = Assert(neededLocal >= RealLit(0), mainError.dueTo(reasons.NegativePermission(e)))
        /*TODO
        val notNull = for (local <- argLocals zip loc) yield {
          Assert(local !== heapModule.translateNull, mainError.dueTo(reasons.))
        }
        */
        val definedness = MaybeCommentBlock("checking if access predicate defined in used state",
          If(b,expModule.checkDefinedness(p, mainError),Statements.EmptyStmt))

        val initPermVars = (neededLocal := permAmount) ++
          (initNeededLocal := permModule.currentPermission(accTransformed.loc)+neededLocal)

        val transferRest = transferAcc(states,used, accTransformed,TransferBoogieVars(tempLocal,b))
        val stmt = definedness ++ assignStmt ++ initPermVars ++  positivePerm ++ transferRest

        mainModule.env.undefine(SILtempLocal)
        argLocals.foreach(v => mainModule.env.undefine(v))

        MaybeCommentBlock("Transfer of " + e.toString(), stmt)
      case _ => sys.error("This version only supports access predicates for packaging of wands")
    }
  }

  /*
   * Precondition: current state is set to the used state
    */
  private def transferAcc(states: List[StateSnapshot], used:StateSnapshot, e: sil.AccessPredicate, vars: TransferBoogieVars):Stmt = {
    val TransferBoogieVars(tempLocal, b) = vars
    states match {
    case (top :: xs) =>
        val addToUsed = (components flatMap (_.transferAdd(e,b))) ++
                      exchangeAssumesWithBoolean(stateModule.assumeGoodState, b)
        val equateLHS = heapModule.translateLocationAccess(e.loc)

        //check definedness of e in state x
        stateModule.restoreState(top)
        val equateStmt = e match {
          case sil.FieldAccessPredicate(field_loc,_) => b := b && equateLHS === heapModule.translateLocationAccess(field_loc)
          case sil.PredicateAccessPredicate(pred_loc,_) => b := b && equateLHS === heapModule.translateLocationAccess(pred_loc)
        }

        val definednessTop:Stmt = (boolTransferTop := TrueLit()) ++
          (generateStmtCheck(components flatMap (_.transferValid(e)), boolTransferTop))
        val minStmt = If(neededLocal <= curpermLocal, tempLocal := neededLocal, tempLocal := curpermLocal)
        val curPermTop = permModule.currentPermission(e.loc)
        val removeFromTop = heapModule.beginExhale ++
          (components flatMap (_.transferRemove(e,b))) ++
           exchangeAssumesWithBoolean(heapModule.endExhale,b) ++
           exchangeAssumesWithBoolean(stateModule.assumeGoodState, b)

        stateModule.restoreState(used)


        MaybeCommentBlock("transfer code for top state of stack",
          Comment("accumulate constraints which need to be satisfied for transfer to occur") ++ definednessTop ++
          Comment("actual code for the transfer from current state on stack") ++
            If(b && boolTransferTop && neededLocal > boogieNoPerm,
              (curpermLocal := curPermTop) ++
                minStmt ++
                If(tempLocal > boogieNoPerm,

                  (neededLocal := neededLocal - tempLocal) ++
                  addToUsed ++
                    equateStmt ++
                  removeFromTop,

                  Nil),

                Nil
              )
        ) ++ transferAcc(xs,used,e,vars)
      case Nil =>
        val curPermUsed = permModule.currentPermission(e.loc)
        Assert(b ==> (neededLocal === boogieNoPerm && curPermUsed === initNeededLocal), mainError.dueTo(reasons.InsufficientPermission(e.loc)))

        /**
         * actually only curPermUsed === permLocal would be sufficient if the transfer is written correctly, since
         * the two conjuncts should be equivalent in theory, but to be safe we ask for the conjunction to hold
         * in case of bugs
         * */
    }
  }

 def evalArgsAccessPredicate(acc: sil.AccessPredicate, permLocal: Option[sil.LocalVar],error: PartialVerificationError,
                              b: Option[LocalVar]):
      (Seq[sil.LocalVar],sil.AccessPredicate,Stmt) = {

    val newPerm = permLocal match {
      case Some(p) => p
      case None => acc.perm
    }

    acc match {
      case sil.FieldAccessPredicate(loc,perm) =>
        val SILrcvLocal = mainModule.env.makeUniquelyNamed(SILrcvLocalDecl).localVar
        val rcvLocal = mainModule.env.define(SILrcvLocal) //bind Boogie to Silver variable
        val assignStmt = rcvLocal := expModule.translateExp(loc.rcv)

        val newLocation = sil.FieldAccess(SILrcvLocal, loc.field)(acc.pos,acc.info)
        val nullCheck:Stmt = Assert((b.get ==> heapModule.checkNonNullReceiver(newLocation)),error.dueTo(reasons.ReceiverNull(loc)))
        (Seq(SILrcvLocal), sil.FieldAccessPredicate(newLocation,newPerm)(acc.pos,acc.info),assignStmt++nullCheck)

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
          sil.PredicateAccess(localEvalArgs, loc.predicateName)(loc.pos, loc.info), newPerm)(acc.pos, acc.info)

        (localEvalArgs, predAccTransformed, assignStmt)
    }

}

/*
  def evalArgsAccessPredicate( e: Seq[sil.Exp],mainName:String): (Seq[(LocalVar,sil.LocalVar,sil.Exp)]) = {
    for (arg <- e) yield {
      val decl = mainModule.env.makeUniquelyNamed(sil.LocalVarDecl(mainName, arg.typ)(arg.pos, arg.info))
      val localVar = decl.localVar
      (mainModule.env.define(localVar), localVar, arg)
    }
  }
*/

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
  case class PackageSetup(hypState: StateSnapshot, usedState: StateSnapshot, initStmt: Stmt, boolVar: LocalVar)

  case class UsedStateSetup(usedState: StateSnapshot, initStmt: Stmt, boolVar: LocalVar)


}

