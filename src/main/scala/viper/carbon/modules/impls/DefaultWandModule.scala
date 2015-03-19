package viper.carbon.modules.impls


import viper.carbon.modules.WandModule
import viper.carbon.modules.components.TransferComponent
import viper.carbon.verifier.Verifier
import viper.silver.ast._
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.boogie.{Exp, LocalVar, Stmt}
import viper.carbon.boogie.Implicits._

/**
 * Created by Gaurav on 06.03.2015.
 */
class DefaultWandModule(val verifier: Verifier) extends WandModule with TransferComponent {
  import verifier._
  import stateModule._
  import permModule._

/** specific to access predicates transfer START**/,
/* used to pass as expression in AccessPredicate when transfer of permission needed */
  val SILneededLocal: sil.LocalVar = sil.LocalVar("neededTransfer")(sil.Perm)
  /* used to track the permissions still needed to transfer */
  val neededLocal:Exp = LocalVar(Identifier("neededTransfer"), permType)

  val SILcurpermLocal = sil.LocalVar("maskTransfer")(sil.Perm)
  /* used to store the current mask in */
  val curpermLocal = LocalVar(Identifier("maskTransfer"), permType)
/** specific to access predicates transfer END**/

  def name = "Wand Module"

  override def initialize() {
    register(this)
  }

  def translatePackage(p: sil.Package):Stmt = {
    p match {
      case pa@sil.Package(wand) => packageWand(wand)
    }
  }

  private def packageWand(wand: MagicWand): Stmt = {
    wand match {
      case w@sil.MagicWand(left,right) =>
        //create a new empty state to collect the footprint
        val (stmt, state) = stateModule.freshEmptyState("Used")
        stateModule.restoreState(state)
        stmt
    }
  }


  /*generates code that transfers permissions from states to used such that e can be satisfied
  * same as in transfer function given in research paper on support for magic wands in automated verifiers
  * Following Precondition and Postcondition must hold: the state of the StateModule in Carbon must be the used state
  * */

   def exhaleExt(states: List[StateSnapshot], used:StateSnapshot, e: sil.Exp):Stmt = {
    e match {
      case acc@sil.AccessPredicate => transfer(states, used, acc)
      case acc@sil.MagicWand => sys.error("exhaleExtConnective: Magic Wands not yet supported ")
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


  def transferMain(states: List[StateSnapshot], used:StateSnapshot, e: sil.Exp, b: LocalVar):Stmt = {
    e match {
      case sil.MagicWand => sys.error("still need to implement this")
      case p@sil.AccessPredicate(loc,e)  =>
        val s1 = neededLocal := permModule.translatePerm(e) //store the permission to be transferred into a separate variable
        val s2 = transferAcc(states,used, transformAccessPred(p), b)
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
      case FieldAccessPredicate(loc,perm, pos,info) => sil.FieldAccessPredicate(loc,SILneededLocal)(pos,info)
      case PredicateAccessPredicate(loc,perm,pos,info) => PredicateAccessPredicate(loc,SILneededLocal)(pos,info)
    }
  }

  def transferAcc(states: List[StateSnapshot], used:StateSnapshot, e: sil.AccessPredicate, b: LocalVar):Stmt = {
    states match {
      case (x :: xs) =>
        Nil
      case Nil =>
        Nil
    }
  }



  //equate loc in current state with loc in state s (current.equate(s,loc))
  def equate(s: StateSnapshot, loc: LocationAccess): Stmt = {
    val lhs = heapModule.translateLocation(loc)
    val current = stateModule.state
    stateModule.restoreState(s)
    val rhs = heapModule.translateLocation(loc)
    stateModule.restoreState(current)
    lhs := rhs
  }
}

