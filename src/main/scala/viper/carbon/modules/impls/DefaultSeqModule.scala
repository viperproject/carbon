/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.impls

import viper.carbon.modules.SeqModule
import viper.silver.components.StatefulComponent
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.verifier.Verifier
import viper.carbon.boogie.Implicits._
import viper.carbon.modules.impls.dafny_axioms.SequenceAxiomatization
import viper.carbon.modules.components.DefinednessComponent
import viper.silver.ast.{SeqIndex, SeqLength}
import viper.silver.ast.utility.Expressions
import viper.silver.verifier.{PartialVerificationError, errors, reasons}

/**
 * The default implementation of [[viper.carbon.modules.SeqModule]].
 */
class DefaultSeqModule(val verifier: Verifier)
    extends SeqModule
    with DefinednessComponent {

  import verifier._
  import typeModule._
  import expModule._

  /**
   * Have sequences been used so far (to determine if we need to include
   * the sequence axiomatization in the prelude.
   */
  private var used = false

  def name = "Sequence module"
  implicit val namespace = verifier.freshNamespace("seq")

  override def freeAssumptions(e: sil.Exp): Stmt = Statements.EmptyStmt

  override def preamble = {
    if (used) {
      LiteralDecl(SequenceAxiomatization.value)
    } else {
      Nil
    }
  }

  override def start() {
    expModule.register(this)
  }

  override def translateSeqExp(e: sil.Exp): Exp = {
    def t(e: sil.Exp) = translateExp(e)
    used = true
    val typ = translateType(e.typ)
    e match {
      case sil.EmptySeq(elemTyp) =>
        val fa = FuncApp(Identifier("Seq#Empty"), Nil, typ)
        fa.showReturnType = true // needed (in general) to avoid Boogie complaints about ambiguous type variable
        fa
      case s@sil.ExplicitSeq(elems) =>
        elems.toList match {
          case Nil => sys.error("did not expect empty sequence")
          case a :: Nil =>
            FuncApp(Identifier("Seq#Singleton"), t(a), typ)
          case a :: as =>
            translateSeqExp(s.desugared) // desugar into appends and singletons
        }
      case sil.RangeSeq(low, high) =>
        FuncApp(Identifier("Seq#Range"), List(t(low), t(high)), typ)
      case sil.SeqAppend(left, right) =>
        FuncApp(Identifier("Seq#Append"), List(t(left), t(right)), typ)
      case sil.SeqIndex(seq, idx) =>
        FuncApp(Identifier("Seq#Index"), List(t(seq), t(idx)), typ)
      case sil.SeqTake(seq, n) =>
        FuncApp(Identifier("Seq#Take"), List(t(seq), t(n)), typ)
      case sil.SeqDrop(seq, n) =>
        FuncApp(Identifier("Seq#Drop"), List(t(seq), t(n)), typ)
      case sil.SeqContains(elem, seq) =>
        FuncApp(Identifier("Seq#Contains"), List(t(seq), t(elem)), typ)
      case sexp@sil.SeqUpdate(seq, idx, elem) =>
      {
        // translate as (s[..i] ++ ([i] ++ s[i+1..])) (NOTE: this assumes i is in the range, which is not yet checked)
        t(sexp.desugaredAssumingIndexInRange)
       // val s = t(seq)
       // val i = t(idx)
       // val v = t(elem)
       // FuncApp(Identifier("Seq#Append"),List(FuncApp(Identifier("Seq#Take"), List(s,i),typ),FuncApp(Identifier("Seq#Append"),List(FuncApp(Identifier("Seq#Singleton"), v, typ),FuncApp(Identifier("Seq#Drop"), List(s,BinExp(i,Add,IntLit(1))),typ)),typ)),typ)
      }
      case sil.SeqLength(seq) =>
        FuncApp(Identifier("Seq#Length"), t(seq), typ)
      case sil.EqCmp(left, right) =>
        FuncApp(Identifier("Seq#Equal"), List(t(left), t(right)), typ)
      case sil.NeCmp(left, right) =>
        UnExp(Not, FuncApp(Identifier("Seq#Equal"), List(t(left), t(right)), typ))
      case _ => sys.error("not a sequence expression")
    }
  }

  override def translateSeqType(seqType: sil.SeqType): Type = {
    used = true
    NamedType("Seq", translateType(seqType.elementType))
  }


  override def simplePartialCheckDefinedness(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean): Stmt = {
    if(makeChecks)
      e match {
        case si@SeqIndex(s,idx) => {
          val index = translateExp(idx)
          val length = translateSeqExp(SeqLength(s)(s.pos,s.info))
          Assert(BinExp(index,GeCmp,IntLit(0)),error.dueTo(reasons.SeqIndexNegative(s,si))) ++ Assert(BinExp(index,LtCmp,length),error.dueTo(reasons.SeqIndexExceedsLength(s,si)))
        }
        case _ => Nil
      }
    else Nil
  }

  /**
   * Reset the state of this module so that it can be used for new program. This method is called
   * after verifier gets a new program.
   */
  override def reset(): Unit = {
    used = false
  }
}
