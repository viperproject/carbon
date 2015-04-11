package viper.carbon.modules.impls


import org.scalatest.GivenWhenThen
import viper.carbon.modules.WandModule
import viper.carbon.modules.components.{TransferComponent, DefinednessComponent}
import viper.carbon.verifier.Verifier
import viper.carbon.boogie._
import viper.carbon.boogie.Implicits._
import viper.carbon.boogie.Namespace

import viper.silver.verifier.{errors, reasons, PartialVerificationError}
import viper.silver.{ast => sil}

import scala.reflect.internal.util.NoPosition


/**
 * Created by Gaurav on 06.03.2015.
 */


class DefaultWandModule(val verifier: Verifier) extends WandModule {
  import verifier._
  import stateModule._
  import permModule._

  val transferNamespace = verifier.freshNamespace("transfer")

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

  override def transferRemove(e:sil.Exp, cond:Exp): Stmt = {
    Nil
  }

  def transferAdd(e:sil.Exp, cond: Exp): Stmt = {
    Nil
  }

  def transferValid(e:sil.Exp):Seq[(Stmt,Exp)] = {
    Nil
  }

  override def translatePackage(p: sil.Package,error: PartialVerificationError):Stmt = {
    p match {
      case pa@sil.Package(wand) =>
        wand match {
          case w@sil.MagicWand(left,right) =>
            mainError = error //set the default error to be used by all operations
            /**DEFINE STATES **/

            val currentState = stateModule.getCopyState

            //hypothetical state for left hand side of wand
            val hypName = names.createUniqueIdentifier("Hypo")
            val (hypStmt,hypState) = stateModule.freshEmptyState("Hypo")

            //state which is used to check if the wand holds
            val usedName = names.createUniqueIdentifier("Used")
            val (usedStmt, usedState) = stateModule.freshEmptyState(usedName)

            /**DEFINE STATES END **/

            //inhale left hand side to initialize hypothetical state
            stateModule.restoreState(hypState)

            /**create a new boolean variable under which all assumptions belonging to the package are made
              *(which makes sure that the assumptions won't be part of the main state after the package)
              *
              */
            val b = LocalVar(Identifier("b")(transferNamespace), Bool)

            val inhaleLeft = MaybeComment("Inhaling left hand side of current wand into hypothetical state",
                                If(b, stmtModule.translateStmt(sil.Inhale(left)(p.pos,p.info)) , Statements.EmptyStmt ))

            /*Gaurav: the position and info is taken from the Package node, might be misleading, also
             *the InhaleError will be used and not the package error. Might want to duplicate the translateStmt code
             * for an Inhale node.
             */

            stateModule.restoreState(usedState)
            val stmt = hypStmt ++ usedStmt ++ inhaleLeft ++ exec(hypState :: currentState :: Nil, usedState, right, b)

            stateModule.restoreState(currentState)

            stmt

          //TODO: add wand to current state
          case _ => sys.error("Package only defined for wands.")
        }
    }
  }

  def exec(states: List[StateSnapshot], ops: StateSnapshot, e:sil.Exp, b: LocalVar):Stmt = {
    e match {
      case sil.Folding(acc,body) =>
        sys.error("exec: folding not yet supported")
      case sil.Unfolding(acc,body) =>
        sys.error("exec: unfolding not yet supported")
      case sil.Applying(wand, body) =>
        sys.error("exec: applying not yet supported")
      case p@sil.Packaging(wand,body) =>
        //hypothetical state for left hand side of wand
        val hypName = names.createUniqueIdentifier("Hypo")
        val (hypStmt,hypState) = stateModule.freshEmptyState("Hypo")

        //state which is used to check if the wand holds
        val usedName = names.createUniqueIdentifier("Used")
        val (usedStmt, usedState) = stateModule.freshEmptyState(usedName)

        /**DEFINE STATES END **/

        //inhale left hand side to initialize hypothetical state
        stateModule.restoreState(hypState)

        /**create a new boolean variable under which all assumptions belonging to the package are made
          *(which makes sure that the assumptions won't be part of the main state after the package)
          *
          */
        val b_new = LocalVar(Identifier(names.createUniqueIdentifier("b"))(transferNamespace), Bool)

        val inhaleLeft = MaybeComment("Inhaling left hand side of current wand into hypothetical state",
          If(b_new, stmtModule.translateStmt(sil.Inhale(wand.left)(e.pos,e.info)) , Statements.EmptyStmt ))

        stateModule.restoreState(usedState)
        val execInnerWand = exec(hypState :: ops :: states, usedState, wand.right, b_new)

        val packaging =  MaybeCommentBlock("Code for the packaging of wand in" + p.toString(),
          hypStmt ++ usedStmt ++ (b_new := b && b_new) ++ inhaleLeft ++ execInnerWand)

        stateModule.restoreState(ops)
        //TODO add wand
        MaybeCommentBlock("Translating " + p.toString(),
          packaging ++ MaybeCommentBlock("Code for body of " + p.toString(), exec(states,ops,body,b)) )

      case _ =>
        //no ghost operation
        val usedName = names.createUniqueIdentifier("Used")
        val (usedStmt,usedState) = stateModule.freshEmptyState(usedName)
        stateModule.restoreState(usedState)
       usedStmt ++ exhaleExt(ops :: states, usedState,e,b)
    }

  }

  /*generates code that transfers permissions from states to used such that e can be satisfied
    * Precondition: current state is set to the used state
    * */
   def exhaleExt(states: List[StateSnapshot], used:StateSnapshot, e: sil.Exp, b:LocalVar):Stmt = {
    e match {
      case acc@sil.AccessPredicate(_,_) => transferMain(states,used, e, b) //transfer(states, used, acc)
      case acc@sil.MagicWand(_,_) => sys.error("exhaleExtConnective: Magic Wands not yet supported ")
      case acc@sil.And(e1,e2) => exhaleExt(states, used, e1,b) :: exhaleExt(states,used,e2,b) :: Nil
      case acc@sil.Implies(e1,e2) => If(expModule.translateExp(e1), exhaleExt(states,used,e1,b),Statements.EmptyStmt)
      case acc@sil.CondExp(c,e1,e2) => If(expModule.translateExp(c), exhaleExt(states,used,e1,b), exhaleExt(states,used,e1,b))
      case _ => exhaleExtExp(states,used,e,b)
    }
  }

  def exhaleExtExp(states: List[StateSnapshot], used:StateSnapshot, e: sil.Exp, b:LocalVar):Stmt = {
    if(e.isPure) {
      Assert(b ==> expModule.translateExp(e), mainError.dueTo(reasons.AssertionFalse(e)))
    } else {
      Statements.EmptyStmt
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

        val SILrcvLocal = mainModule.env.makeUniquelyNamed(SILrcvLocalDecl).localVar
        val rcvLocal = mainModule.env.define(SILrcvLocal) //bind Boogie to Silver variable

        val permAmount = permModule.translatePerm(perm) //store the permission to be transferred into a separate variable
        val positivePerm = Assert(neededLocal >= RealLit(0), mainError.dueTo(reasons.NegativePermission(e)))
        val definedness = MaybeCommentBlock("checking if access predicate defined in used state",
          expModule.checkDefinedness(p, mainError))

        val rcv: Exp =
          p match {
            case fa: sil.FieldAccessPredicate => (expModule.translateExp(fa.loc.rcv))
            case _ => sys.error("This version only supports transfer of field access predicates")
          }

        val transferRest = transferAcc(states,used, transformAccessPred(p,SILtempLocal, SILrcvLocal),TransferBoogieVars(tempLocal,b))
        val stmt = definedness ++ (rcvLocal := rcv) ++ (initNeededLocal := permAmount) ++
                  (neededLocal := permAmount) ++  positivePerm ++ transferRest

        mainModule.env.undefine(SILtempLocal)
        mainModule.env.undefine(SILrcvLocal)

        MaybeCommentBlock("Transfer of " + e.toString(), stmt)
      case _ => sys.error("This version only supports access predicates for packaging of wands")
    }
  }

  /**
   *
   * @param e Access Predicate to be transformed, generally this is the original predicate from the Silver AST
   * @param localPerm denotes permission in a local variable
*    @param localRCV denotes receiver in a field access predicate
   * @return access predicate where the receiver of the location is changed for field accesses
   *         to the local variable which in Boogie stores the receiver evaluated in the current used state,
   *         also permission is changed to the local variable given as argument
   */
  def transformAccessPred(e: sil.AccessPredicate, localPerm: sil.LocalVar, localRCV:sil.LocalVar):sil.AccessPredicate = {
    e match {
      case p@sil.FieldAccessPredicate(loc,perm) =>
        val newLocation = sil.FieldAccess(localRCV, loc.field)(p.pos,p.info)
        sil.FieldAccessPredicate(newLocation,localPerm)(p.pos,p.info)
      case p@sil.PredicateAccessPredicate(loc,perm) => sil.PredicateAccessPredicate(loc,localPerm)(p.pos,p.info)
    }
  }

  /*
   * Precondition: current state is set to the used state
    */
  def transferAcc(states: List[StateSnapshot], used:StateSnapshot, e: sil.AccessPredicate, vars: TransferBoogieVars):Stmt = {
    val TransferBoogieVars(tempLocal, b) = vars
    states match {
    case (top :: xs) =>
        val addToUsed = (components flatMap (_.transferAdd(e,b))) ++
                      exchangeAssumesWithBoolean(stateModule.assumeGoodState, b)
        val equateLHS = heapModule.translateLocationAccess(e.loc)

        //check definedness of e in state x
        stateModule.restoreState(top)
        val equateRHS = heapModule.translateLocationAccess(e.loc)
        val definednessTop:Stmt = (boolTransferTop := TrueLit()) ++
          (generateStmtCheck(components flatMap (_.transferValid(e)), boolTransferTop))
        val minStmt = If(neededLocal <= curpermLocal, tempLocal := neededLocal, tempLocal := curpermLocal)
        val curPermTop = permModule.currentPermission(e.loc)
        val removeFromTop = (components flatMap (_.transferRemove(e,b))) ++
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
                  (b := b && equateLHS === equateRHS) ++
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

  case class PackageSetup(hypState: StateSnapshot, usedState: StateSnapshot, initStmt: Stmt, boolVar: LocalVar)
}

