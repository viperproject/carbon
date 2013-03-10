package semper.carbon.modules.impls

import semper.carbon.modules.{ExpModule, Verifier, AllModule}
import semper.sil.{ast => sil}
import semper.carbon.boogie._

/**
 * The default implementation of [[semper.carbon.modules.ExpModule]].
 *
 * @author Stefan Heule
 */
class DefaultExpModule(val verifier: Verifier) extends ExpModule with AllModule {
  override def translateExp(e: sil.Exp): Exp = {
    e match {
      case sil.IntLit(i) =>
        IntLit(i)
      case sil.BoolLit(b) =>
        BoolLit(b)
      case sil.NullLit() =>
        TrueLit() // TODO
      case l@sil.LocalVar(name) =>
        LocalVar(name, translateType(l.typ))
      case sil.AbstractLocalVar(n) =>
        TrueLit() // TODO
      case sil.FieldAccess(rcv, field) =>
        TrueLit() // TODO
      case sil.PredicateAccess(rcv, predicate) =>
        TrueLit() // TODO
      case sil.Unfolding(acc, exp) =>
        TrueLit() // TODO
      case sil.Old(exp) =>
        TrueLit() // TODO
      case sil.CondExp(cond, thn, els) =>
        CondExp(translateExp(cond).asInstanceOf[MaybeBool], translateExp(thn), translateExp(els))
      case sil.Exists(v, exp) =>
        TrueLit() // TODO
      case sil.Forall(v, exp) =>
        TrueLit() // TODO
      case sil.ReadPerm() =>
        TrueLit() // TODO
      case sil.WildCardPerm() =>
        TrueLit() // TODO
      case sil.FullPerm() =>
        TrueLit() // TODO
      case sil.NoPerm() =>
        TrueLit() // TODO
      case sil.EpsilonPerm() =>
        TrueLit() // TODO
      case sil.CurrentPerm(loc) =>
        TrueLit() // TODO
      case sil.ConcretePerm(a, b) =>
        TrueLit() // TODO
      case sil.AccessPredicate(loc, perm) =>
        TrueLit() // TODO
      case sil.BinExp(left, right) =>
        TrueLit() // TODO
      case sil.UnExp(exp) =>
        TrueLit() // TODO
      case sil.FuncApp(func, rcv, args) =>
        TrueLit() // TODO
      case sil.DomainFuncApp(func, args) =>
        TrueLit() // TODO
    }
  }
}
