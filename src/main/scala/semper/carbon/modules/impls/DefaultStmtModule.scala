package semper.carbon.modules.impls

import semper.carbon.modules.StmtModule
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier
import Implicits._
import semper.sil.verifier.{PartialVerificationError, errors}
import semper.carbon.modules.components.StmtComponent

/**
 * The default implementation of a [[semper.carbon.modules.StmtModule]].
 *
 * @author Stefan Heule
 */
class DefaultStmtModule(val verifier: Verifier) extends StmtModule with StmtComponent {

  import verifier._
  import expModule._
  import stateModule._
  import exhaleModule._
  import inhaleModule._

  // registering in the constructor ensures that this will be the first component
  register(this)

  val lblNamespace = verifier.freshNamespace("stmt.lbl")

  def name = "Statement module"

  override def handleStmt(stmt: sil.Stmt): Stmt = {
    stmt match {
      case assign@sil.LocalVarAssign(lhs, rhs) =>
        checkDefinedness(lhs, errors.AssignmentFailed(assign)) ++
          checkDefinedness(rhs, errors.AssignmentFailed(assign)) ++
          Assign(translateExp(lhs), translateExp(rhs))
      case assign@sil.FieldAssign(lhs, rhs) =>
        checkDefinedness(lhs, errors.AssignmentFailed(assign)) ++
          checkDefinedness(rhs, errors.AssignmentFailed(assign))
      case sil.Fold(e) =>
        ???
      case sil.Unfold(e) =>
        ???
      case inh@sil.Inhale(e) =>
        checkDefinedness(e, errors.InhaleFailed(inh)) ++
          inhale(e)
      case exh@sil.Exhale(e) =>
        checkDefinedness(e, errors.ExhaleFailed(exh)) ++
          exhale((e, errors.ExhaleFailed(exh)))
      case a@sil.Assert(e) =>
        if (e.isPure) {
          // if e is pure, then assert and exhale are the same
          checkDefinedness(e, errors.AssertFailed(a)) ++
            exhale((e, errors.AssertFailed(a)))
        } else {
          // we create a temporary state to ignore the side-effects
          val (backup, snapshot) = freshTempState
          val exhaleStmt = exhale((e, errors.AssertFailed(a)))
          restoreState(snapshot)
          checkDefinedness(e, errors.AssertFailed(a)) :: backup :: exhaleStmt :: Nil
        }
      case mc@sil.MethodCall(method, args, targets) =>
        (targets map (e => checkDefinedness(e, errors.CallFailed(mc)))) ++
          (args map (e => checkDefinedness(e, errors.CallFailed(mc)))) ++
          Havoc((targets map translateExp).asInstanceOf[Seq[Var]]) ++
          MaybeCommentBlock("Exhaling precondition", exhale(mc.pres map (e => (e, errors.PreconditionInCallFalse(mc))))) ++
          MaybeCommentBlock("Inhaling postcondition", inhale(mc.posts))
      case sil.While(cond, invs, locals, body) =>
        ???
      case fb@sil.FreshReadPerm(vars, body) =>
          MaybeCommentBlock(s"Start of fresh(${vars.mkString(", ")})", components map (_.enterFreshBlock(fb))) ++
          translateStmt(body) ++
          MaybeCommentBlock(s"End of fresh(${vars.mkString(", ")})", components map (_.leaveFreshBlock(fb)))
      case i@sil.If(cond, thn, els) =>
        checkDefinedness(cond, errors.IfFailed(i)) ++
          If(translateExp(cond),
            translateStmt(thn),
            translateStmt(els))
      case sil.Label(name) =>
        Label(Lbl(Identifier(name)(lblNamespace)))
      case sil.Goto(target) =>
        Goto(Lbl(Identifier(target)(lblNamespace)))
      case sil.NewStmt(lhs) =>
        Nil
      case _: sil.Seqn =>
        Nil
    }
  }

  override def translateStmt(stmt: sil.Stmt): Stmt = {
    var comment = "Translating statement: " + stmt.toString
    stmt match {
      case sil.Seqn(ss) =>
        // return to avoid adding a comment, and to avoid the extra 'assumeGoodState'
        return Seqn(ss map translateStmt)
      case sil.If(cond, thn, els) =>
        comment = s"Translating statement: if ($cond)"
      case fb@sil.FreshReadPerm(vars, body) =>
        comment = s"Translating statement: fresh(${vars.mkString(", ")})"
      case _ =>
    }
    val all = Seqn(components map (_.handleStmt(stmt)))
    if (all.children.size == 0) {
      assert(assertion = false, "Translation of " + stmt + " is not defined")
    }
    val translation = all ::
      assumeGoodState ::
      Nil
    CommentBlock(comment + s" -- ${stmt.pos}", translation)
  }

  /**
   * Check definedness of SIL expression connectives (such as logical and/implication) and forwards the
   * checking of other expressions to the definedness components.
   */
  def checkDefinedness(e: sil.Exp, error: PartialVerificationError): Stmt = {
    e match {
      case sil.And(e1, e2) =>
        checkDefinedness(e1, error) ::
          checkDefinedness(e2, error) ::
          Nil
      case sil.Implies(e1, e2) =>
        If(translateExp(e1), checkDefinedness(e2, error), Statements.EmptyStmt)
      case sil.CondExp(c, e1, e2) =>
        If(translateExp(c), checkDefinedness(e1, error), checkDefinedness(e2, error))
      case _ =>
        val stmt = definednessComponents map (_.checkDefinedness(e, error))
        val stmt2 = for (sub <- e.subnodes if sub.isInstanceOf[sil.Exp]) yield {
          checkDefinedness(sub.asInstanceOf[sil.Exp], error)
        }
        stmt ++ stmt2
    }
  }
}
