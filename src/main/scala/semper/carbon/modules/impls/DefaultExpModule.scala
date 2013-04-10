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

  import verifier._
  import typeModule._
  import heapModule._
  import mainModule._
  import domainModule._
  import seqModule._

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
        env.define(v.localVar)
        Exists(Seq(translateLocalVarDecl(v)), translateExp(exp))
      case sil.Forall(v, triggers, exp) =>
        env.define(v.localVar)
        val ts = triggers map (t => Trigger(t.exps map translateExp))
        Forall(Seq(translateLocalVarDecl(v)), ts, translateExp(exp))
      case sil.WildcardPerm() =>
        ???
      case sil.FullPerm() =>
        ???
      case sil.NoPerm() =>
        ???
      case sil.EpsilonPerm() =>
        ???
      case sil.CurrentPerm(loc) =>
        ???
      case sil.FractionalPerm(left, right) =>
        ???
      case sil.AccessPredicate(loc, perm) =>
        sys.error("not handled by expression module")
      case sil.EqCmp(left, right) =>
        if (left.typ.isInstanceOf[sil.SeqType]) {
          translateSeqExp(e)
        } else {
          BinExp(translateExp(left), EqCmp, translateExp(right))
        }
      case sil.NeCmp(left, right) =>
        if (left.typ.isInstanceOf[sil.SeqType]) {
          translateSeqExp(e)
        } else {
          BinExp(translateExp(left), NeCmp, translateExp(right))
        }
      case sil.DomainBinExp(left, op, right) =>
        val bop = op match {
          case sil.OrOp => Or
          case sil.LeOp => LeCmp
          case sil.LtOp => LtCmp
          case sil.GeOp => GeCmp
          case sil.GtOp => GtCmp
          case sil.AddOp => Add
          case sil.SubOp => Sub
          case sil.DivOp => IntDiv
          case sil.ModOp => Mod
          case sil.MulOp => Mul
          case sil.AndOp | sil.ImpliesOp =>
            sys.error("&& and ==> are not handled in expression module")
          case sil.PermGeOp | sil.PermGtOp | sil.PermLeOp | sil.PermLtOp |
               sil.PermAddOp | sil.PermMulOp | sil.PermSubOp | sil.IntPermMulOp |
               sil.FracOp =>
            sys.error("permission operations not handled in expression module")
        }
        BinExp(translateExp(left), bop, translateExp(right))
      case sil.Neg(exp) =>
        UnExp(Neg, translateExp(exp))
      case sil.Not(exp) =>
        UnExp(Not, translateExp(exp))
      case sil.FuncApp(func, args) =>
        ???
      case fa@sil.DomainFuncApp(func, args, _) =>
        translateDomainFuncApp(fa)
      case seqExp@sil.EmptySeq(elemTyp) =>
        translateSeqExp(seqExp)
      case seqExp@sil.ExplicitSeq(elems) =>
        translateSeqExp(seqExp)
      case seqExp@sil.RangeSeq(low, high) =>
        translateSeqExp(seqExp)
      case seqExp@sil.SeqAppend(left, right) =>
        translateSeqExp(seqExp)
      case seqExp@sil.SeqIndex(seq, idx) =>
        translateSeqExp(seqExp)
      case seqExp@sil.SeqTake(seq, n) =>
        translateSeqExp(seqExp)
      case seqExp@sil.SeqDrop(seq, n) =>
        translateSeqExp(seqExp)
      case seqExp@sil.SeqContains(elem, seq) =>
        translateSeqExp(seqExp)
      case seqExp@sil.SeqUpdate(seq, idx, elem) =>
        translateSeqExp(seqExp)
      case seqExp@sil.SeqLength(seq) =>
        translateSeqExp(seqExp)
    }
  }
}
