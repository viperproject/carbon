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
/**
 * Created by Gaurav on 06.03.2015.
 */


class DefaultWandModule(val verifier: Verifier) extends WandModule with TransferComponent with DefinednessComponent {
  import verifier._
  import stateModule._
  import permModule._

  val transferNamespace = verifier.freshNamespace("transfer")

  /**Gaurav: still need to worry about namespaces/scopes **/
  /** specific to access predicates transfer START**/
/* used to pass as expression in AccessPredicate when transfer of permission needed */
  //val SILneededLocal: sil.LocalVar = sil.LocalVar("neededTransfer")(sil.Perm)
  val SILtempLocal: sil.LocalVar = sil.LocalVar("neededTransfer")(sil.Perm)

  val tempLocal: LocalVar = mainModule.env.define(SILtempLocal)

  /* used to track the permissions still needed to transfer */
  val neededLocal = LocalVar(Identifier("neededTransfer")(transferNamespace), permType)

  val SILcurpermLocal = sil.LocalVar("maskTransfer")(sil.Perm)
  /* used to store the current mask in */
  val curpermLocal = LocalVar(Identifier("maskTransfer")(transferNamespace), permType)
/** specific to access predicates transfer END**/

  val boolTransferUsed = LocalVar(Identifier("accVar1"), Bool)
  val boolTransferTop = LocalVar(Identifier("accVar2"), Bool)


  //use this to generate unique names for states
  private val names = new BoogieNameGenerator()


  def name = "Wand Module"

  override def initialize() {
    register(this)
  }

  override def translatePackage(p: sil.Package,error: PartialVerificationError):Stmt = {
    p match {
      case pa@sil.Package(wand) =>
        wand match {
          case w@sil.MagicWand(left,right) =>
            //val definedness = expModule.checkDefinedness()

            /**DEFINE STATES **/

            val currentState = stateModule.state
            //hypothetical state for left hand side of wand
            val hypName = names.createUniqueIdentifier("Hypo")
            val (hypStmt,hypState) = stateModule.freshEmptyState("Hypo")

            //state which is used to check if the wand holds
            val usedName = names.createUniqueIdentifier("Used")
            val (usedStmt, usedState) = stateModule.freshEmptyState(usedName)

            /**DEFINE STATES END **/


            val emptyState = hypStmt++usedStmt
            //inhale left hand side to initialize hypothetical state
            stateModule.restoreState(hypState)
            val inhaleLeft = stmtModule.translateStmt(sil.Inhale(left)(p.pos,p.info))

            /*Gaurav: the position and info is taken from the Package node, might be misleading, also
             *the InhaleError will be used and not the package error. Might want to duplicate the translateStmt code
             * for an Inhale node.
             */

            stateModule.restoreState(usedState)
            Nil
        }
    }
  }

  /*generates code that transfers permissions from states to used such that e can be satisfied*/
   def exhaleExt(states: List[StateSnapshot], used:StateSnapshot, e: sil.Exp):Stmt = {
    e match {
      case acc@sil.AccessPredicate(_,_) => Nil //transfer(states, used, acc)
      case acc@sil.MagicWand(_,_) => sys.error("exhaleExtConnective: Magic Wands not yet supported ")
      case acc@sil.And(e1,e2) => exhaleExt(states, used, e1) :: exhaleExt(states,used,e2) :: Nil
      case acc@sil.Implies(e1,e2) => If(expModule.translateExp(e1), exhaleExt(states,used,e1),Statements.EmptyStmt)
      case acc@sil.CondExp(c,e1,e2) => If(expModule.translateExp(c), exhaleExt(states,used,e1), exhaleExt(states,used,e1))
      case _ => exhaleExtExp(states,used,e)
    }

  }

  def exhaleExtExp(states: List[StateSnapshot], used:StateSnapshot, e: sil.Exp):Stmt = {
    if(e.isPure) {
      //wrap in if condition on b
      Assert(expModule.translateExp(e), null)
    } else {
      Statements.EmptyStmt
    }
  }


  def transferMain(states: List[StateSnapshot], used:StateSnapshot, e: sil.Exp, b: LocalVar,error:PartialVerificationError):Stmt = {
    e match {
      case sil.MagicWand(left,right) => sys.error("still need to implement this")
      case p@sil.AccessPredicate(loc,e)  =>
        val s1 = neededLocal := permModule.translatePerm(e) //store the permission to be transferred into a separate variable
        val definedness = MaybeCommentBlock("checking if access predicate defined in used state",
                            expModule.checkDefinedness(e, error))
        val positivePerm = Assert(neededLocal >= RealLit(0), error.dueTo(reasons.NegativePermission(e)))
        val s2 = transferAcc(states,used, transformAccessPred(p))
        s1 ++ s2
      case _ => sys.error("This version only supports access predicates for packaging of wands")
    }
  }

  /**
   * returns the access predicate with the same location as the input access predicate but sets the permission to the
   * local variable "SILneededLocal"
   */
  def transformAccessPred(e: sil.AccessPredicate):sil.AccessPredicate = {
    e match {
      case p@sil.FieldAccessPredicate(loc,perm) => sil.FieldAccessPredicate(loc,SILtempLocal)(p.pos,p.info)
      case p@sil.PredicateAccessPredicate(loc,perm) => sil.PredicateAccessPredicate(loc,SILtempLocal)(p.pos,p.info)
    }
  }

  def transferAcc(states: List[StateSnapshot], used:StateSnapshot, e: sil.AccessPredicate,cond:Exp):Stmt = {
    states match {
      case (x :: xs) =>
        val currentState = stateModule.state
        //check definedness of e in state x
        stateModule.restoreState(used)
        val definednessUsed =
          Havoc(boolTransferUsed)++ (boolTransferUsed := TrueLit()) ++
            exchangeAssertsWithBoolean(expModule.checkDefinedness(e,),boolTransferUsed)
        stateModule.restoreState(x)
        val definednessTop:Stmt = Havoc(boolTransferTop) ++ (boolTransferTop := TrueLit()) ++
          (generateStmtCheck(components flatMap (_.transferValid(e)), boolTransferTop))

        val transferComplete = Havoc(tempLocal)++ transferAccOnce(x,used,e) ++ (neededLocal := RealLit(0))

        val curPerm = permModule.currentPermission(e.loc)
        val transferPartial = Havoc(tempLocal) ++
          (tempLocal := curPerm) ++ transferAccOnce(x,used,e) ++ (neededLocal := neededLocal - curPerm)

        stateModule.restoreState(currentState)

        Havoc(tempLocal)++(tempLocal := neededLocal) ++ definednessUsed ++ definednessTop ++
          If(boolTransferUsed&&boolTransferTop,
            transferComplete, Statements.EmptyStmt) ++
        Havoc(tempLocal)++ (tempLocal := curPerm) ++ definednessUsed ++ definednessTop ++
        If(boolTransferUsed&&boolTransferTop,
          transferPartial, Statements.EmptyStmt) ++
        transferAcc(xs,used, e,cond)
      case Nil =>
        Nil
    }
  }

  def transferAccOnce(top: StateSnapshot, used: StateSnapshot, e: sil.AccessPredicate,cond:Exp):Stmt = {
    val currentState = stateModule.state
    stateModule.restoreState(top)
    val addToUsed = components map (_.transferAdd(e,))
    val equateLoc = equate(top, e.loc)
    stateModule.restoreState(top)
    val removeFromTop = components map (_.transferRemove(e,))
    stateModule.restoreState(currentState)

    addToUsed++If(cond, equateLoc, Statements.EmptyStmt)++removeFromTop
  }



  //equate loc in current state with loc in state s (current.equate(s,loc))
  def equate(s: StateSnapshot, loc: sil.LocationAccess): Stmt = {
    val lhs = heapModule.translateLocation(loc)
    val current = stateModule.state
    stateModule.restoreState(s)
    val rhs = heapModule.translateLocation(loc)
    stateModule.restoreState(current)
    Assume(lhs === rhs)
  }


   /*
    *transforms a statement such that it doesn't have any asserts anymore and all asserted expressions
    * are accumulated in a single variable, i.e.:
    *
    * Assert x != null
    * Assert y >= 0 is transformed to:
    * b = b && x!= null; b = b && y >= 0
    */
  def exchangeAssertsWithBoolean(stmt: Stmt,boolVar: LocalVar):Stmt = {
    stmt match {
      case AssertImpl(exp,error) =>
        boolVar := (boolVar && exp)
      case Seqn(statements) =>
       Seqn(statements.map(s => exchangeAssertsWithBoolean(s, boolVar)))
      case If(c,thn,els) =>
        If(c,exchangeAssertsWithBoolean(thn,boolVar),exchangeAssertsWithBoolean(els,boolVar))
      case NondetIf(c,thn,els) =>
        NondetIf(c,exchangeAssertsWithBoolean(thn,boolVar))
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
}

