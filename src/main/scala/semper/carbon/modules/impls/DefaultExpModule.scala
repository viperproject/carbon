package semper.carbon.modules.impls

import semper.carbon.modules.ExpModule
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier
import semper.sil.verifier.PartialVerificationError
import semper.carbon.boogie.Implicits._

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
  import permModule._
  import stateModule._

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
        translateLocalVar(l)
      case sil.Result() =>
        ???
      case f@sil.FieldAccess(rcv, field) =>
        translateFieldAccess(f)
      case sil.PredicateAccess(rcv, predicate) =>
        ???
      case sil.Unfolding(acc, exp) =>
        ???
      case sil.Old(exp) =>
        val snapshot = stateModule.makeOldState
        val res = translateExp(exp)
        stateModule.restoreState(snapshot)
        res
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
        translatePerm(e)
      case sil.FullPerm() =>
        translatePerm(e)
      case sil.NoPerm() =>
        translatePerm(e)
      case sil.EpsilonPerm() =>
        translatePerm(e)
      case sil.CurrentPerm(loc) =>
        translatePerm(e)
      case sil.FractionalPerm(left, right) =>
        translatePerm(e)
      case sil.AccessPredicate(loc, perm) =>
        sys.error("not handled by expression module")
      case sil.EqCmp(left, right) =>
        if (left.typ.isInstanceOf[sil.SeqType]) {
          translateSeqExp(e)
        } else if (left.typ == sil.Perm) {
          translatePermComparison(e)
        } else {
          BinExp(translateExp(left), EqCmp, translateExp(right))
        }
      case sil.NeCmp(left, right) =>
        if (left.typ.isInstanceOf[sil.SeqType]) {
          translateSeqExp(e)
        } else if (left.typ == sil.Perm) {
          translatePermComparison(e)
        } else {
          BinExp(translateExp(left), NeCmp, translateExp(right))
        }
      case sil.DomainBinExp(_, sil.PermGeOp, _) |
           sil.DomainBinExp(_, sil.PermGtOp, _) |
           sil.DomainBinExp(_, sil.PermLeOp, _) |
           sil.DomainBinExp(_, sil.PermLtOp, _) =>
        translatePermComparison(e)
      case sil.DomainBinExp(_, sil.PermAddOp, _) |
           sil.DomainBinExp(_, sil.PermMulOp, _) |
           sil.DomainBinExp(_, sil.PermSubOp, _) |
           sil.DomainBinExp(_, sil.IntPermMulOp, _) |
           sil.DomainBinExp(_, sil.FracOp, _) =>
        translatePerm(e)
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
          case _ =>
            sys.error("should be handeled further above")
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

  override def translateLocalVar(l: sil.LocalVar): LocalVar = {
    LocalVar(Identifier(l.name)(verifier.mainModule.silVarNamespace), translateType(l.typ))
  }

  override def checkDefinedness(e: sil.Exp, error: PartialVerificationError): Stmt = {
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
        def translate: Seqn = {
          val stmt = components map (_.checkDefinedness(e, error))
          val stmt2 = for (sub <- e.subnodes if sub.isInstanceOf[sil.Exp]) yield {
            checkDefinedness(sub.asInstanceOf[sil.Exp], error)
          }
          stmt ++ stmt2
        }
        if (e.isInstanceOf[sil.Old]) {
          val snapshot = makeOldState
          val res = translate
          restoreState(snapshot)
          res
        } else {
          translate
        }
    }
  }

  override def checkDefinednessOfSpec(e: sil.Exp, error: PartialVerificationError): Stmt = {
    Nil
  }
}
