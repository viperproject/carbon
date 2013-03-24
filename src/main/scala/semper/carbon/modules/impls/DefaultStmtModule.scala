package semper.carbon.modules.impls

import semper.carbon.modules.StmtModule
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier
import Implicits._
import semper.sil.verifier.errors
import semper.carbon.modules.components.StmtComponent

/**
 * The default implementation of a [[semper.carbon.modules.StmtModule]].
 *
 * @author Stefan Heule
 */
class DefaultStmtModule(val verifier: Verifier) extends StmtModule with StmtComponent {

  import verifier.expModule._
  import verifier.stateModule._
  import verifier.exhaleModule._

  // registering in the constructor ensures that this will be the first component
  register(this)

  val lblNamespace = verifier.freshNamespace("stmt.lbl")

  def name = "Statement module"

  override def handleStmt(stmt: sil.Stmt): Stmt = {
    stmt match {
      case sil.LocalVarAssign(lhs, rhs) =>
        Assign(translateExp(lhs), translateExp(rhs))
      case sil.Fold(e) =>
        ???
      case sil.Unfold(e) =>
        ???
      case sil.Inhale(e) =>
        ???
      case exh@sil.Exhale(e) =>
        exhale((e, errors.ExhaleFailed(exh)))
      case sil.MethodCall(m, rcv, args, targets) =>
        ???
      case sil.While(cond, invs, locals, body) =>
        ???
      case sil.If(cond, thn, els) =>
        If(translateExp(cond),
          translateStmt(thn),
          translateStmt(els))
      case sil.Label(name) =>
        Label(Lbl(Identifier(name)(lblNamespace)))
      case sil.Goto(target) =>
        Goto(Lbl(Identifier(target)(lblNamespace)))
      case sil.FreshReadPerm(vars, body) =>
        ???
      case _ =>
        Statements.EmptyStmt
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
      case sil.FreshReadPerm(vars, body) =>
        comment = s"Translating statement: fresh(${vars.mkString(", ")})"
      case _ =>
    }
    val all = Seqn(components map (_.handleStmt(stmt)))
    if (all.children.size == 0) {
      assert(false, "Translation of " + stmt + " is not defined")
    }
    val translation = all ::
      assumeGoodState ::
      Nil
    CommentBlock(comment + s" -- ${stmt.pos}", translation)
  }
}
