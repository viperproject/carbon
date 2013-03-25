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
  import verifier.heapModule._

  def name = "Expression module"
  override def translateExp(e: sil.Exp): Exp = {
    e match {
      case sil.IntLit(i) =>
        IntLit(i)
      case sil.BoolLit(b) =>
        BoolLit(b)
      case sil.NullLit() =>
        translateNull
      case l@sil.LocalVar(name) =>
        LocalVar(Identifier(name)(verifier.mainModule.silVarNamespace), translateType(l.typ))
      case sil.ThisLit() =>
        translateThis
      case sil.Result() =>
        ???
      case f@sil.FieldAccess(rcv, field) =>
        translateFieldAccess(f)
      case sil.PredicateAccess(rcv, predicate) =>
        ???
      case sil.Unfolding(acc, exp) =>
        ???
      case sil.Old(exp) =>
        ???
      case sil.CondExp(cond, thn, els) =>
        CondExp(translateExp(cond), translateExp(thn), translateExp(els))
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
      case sil.EqCmp(left, right) =>
        BinExp(translateExp(left), EqCmp, translateExp(right))
      case sil.NeCmp(left, right) =>
        BinExp(translateExp(left), NeCmp, translateExp(right))
      case sil.DomainBinExp(left, op, right) =>
        val bop = op match {
          case sil.OrOp => Or
          case sil.LeOp => LeCmp
          case sil.LtOp => LtCmp
          case sil.GeOp => GeCmp
          case sil.GtOp => GtCmp
          case sil.AddOp => Add
          case sil.SubOp => Sub
          case sil.DivOp => Div
          case sil.ModOp => Mod
          case _ => ???
        }
        BinExp(translateExp(left), bop, translateExp(right))
      case b@sil.BinExp(left, right) =>
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
