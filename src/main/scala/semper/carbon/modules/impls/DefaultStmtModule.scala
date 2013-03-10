package semper.carbon.modules.impls

import semper.carbon.modules.{Verifier, AllModule, StmtModule}
import semper.sil.{ast => sil}
import semper.carbon.boogie._

/**
 * The default implementation of a [[semper.carbon.modules.StmtModule]].
 *
 * @author Stefan Heule
 */
class DefaultStmtModule(val verifier: Verifier) extends StmtModule with AllModule {
  def name = "Statement module"
  override def translateStmt(stmt: sil.Stmt): Stmt = {
    val translation = stmt match {
      case sil.LocalVarAssign(lhs, rhs) =>
        Assign(translateExp(lhs).asInstanceOf[Lhs], translateExp(rhs))
      case sil.FieldAssign(lhs, rhs) =>
        ???
      case sil.Fold(e) =>
        ???
      case sil.Unfold(e) =>
        ???
      case sil.Inhale(e) =>
        ???
      case sil.Exhale(e) =>
        // TODO: use the exhale module
        Assert(translateExp(e))
      case sil.MethodCall(m, rcv, args, targets) =>
        ???
      case sil.Seqn(ss) =>
        Seqn(ss map translateStmt)
      case sil.While(cond, invs, locals, body) =>
        ???
      case sil.If(cond, thn, els) =>
        ???
      case sil.Label(name) =>
        ???
      case sil.Goto(target) =>
        ???
      case sil.FreshReadPerm(vars, body) =>
        ???
    }
    CommentBlock("-- Translation of statement: " + stmt.toString, translation)
  }
}
