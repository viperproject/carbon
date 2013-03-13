package semper.carbon.modules.impls

import semper.carbon.modules.ExpModule
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier

/**
 * The default implementation of [[semper.carbon.modules.ExpModule]].
 *
 * @author Stefan Heule
 */
class DefaultExpModule(val verifier: Verifier) extends ExpModule {

  import verifier.typeModule._

  def name = "Expression module"
  override def translateExp(e: sil.Exp): Exp = {
    e match {
      case sil.IntLit(i) =>
        IntLit(i)
      case sil.BoolLit(b) =>
        BoolLit(b)
      case sil.NullLit() =>
        ???
      case l@sil.LocalVar(name) =>
        LocalVar(name, translateType(l.typ))
      case sil.AbstractLocalVar(n) =>
        ???
      case sil.FieldAccess(rcv, field) =>
        ???
      case sil.PredicateAccess(rcv, predicate) =>
        ???
      case sil.Unfolding(acc, exp) =>
        ???
      case sil.Old(exp) =>
        ???
      case sil.CondExp(cond, thn, els) =>
        CondExp(translateExp(cond).asInstanceOf[MaybeBool], translateExp(thn), translateExp(els))
      case sil.Exists(v, exp) =>
        ???
      case sil.Forall(v, exp) =>
        ???
      case sil.ReadPerm() =>
        ???
      case sil.WildCardPerm() =>
        ???
      case sil.FullPerm() =>
        ???
      case sil.NoPerm() =>
        ???
      case sil.EpsilonPerm() =>
        ???
      case sil.CurrentPerm(loc) =>
        ???
      case sil.ConcretePerm(a, b) =>
        ???
      case sil.AccessPredicate(loc, perm) =>
        ???
      case sil.BinExp(left, right) =>
        ???
      case sil.UnExp(exp) =>
        ???
      case sil.FuncApp(func, rcv, args) =>
        ???
      case sil.DomainFuncApp(func, args) =>
        ???
    }
  }
}
