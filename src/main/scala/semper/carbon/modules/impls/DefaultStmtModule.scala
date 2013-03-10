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
  override def translateStmt(stmt: sil.Stmt): Stmt = {
    stmt match {
      case sil.LocalVarAssign(lhs, rhs) =>
        Assign(translateExp(lhs).asInstanceOf[Lhs], translateExp(rhs))
      case sil.FieldAssign(lhs, rhs) =>
        Seqn(Nil) // TODO
      case sil.Fold(e) =>
        Seqn(Nil) // TODO
      case sil.Unfold(e) =>
        Seqn(Nil) // TODO
      case sil.Inhale(e) =>
        Seqn(Nil) // TODO
      case sil.Exhale(e) =>
        // TODO: use the exhale module
        Assert(translateExp(e))
      case sil.MethodCall(m, rcv, args, targets) =>
        Seqn(Nil) // TODO
      case sil.Seqn(ss) =>
        Seqn(Nil) // TODO
      case sil.While(cond, invs, locals, body) =>
        Seqn(Nil) // TODO
      case sil.If(cond, thn, els) =>
        Seqn(Nil) // TODO
      case sil.Label(name) =>
        Seqn(Nil) // TODO
      case sil.Goto(target) =>
        Seqn(Nil) // TODO
      case sil.FreshReadPerm(vars, body) =>
        Seqn(Nil) // TODO
    }
  }
}
