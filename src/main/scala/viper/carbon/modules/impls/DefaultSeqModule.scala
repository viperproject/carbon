/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.impls

import viper.carbon.modules.SeqModule
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.verifier.Verifier
import viper.carbon.boogie.Implicits._
import viper.carbon.modules.impls.dafny_axioms.SequenceAxiomatization

/**
 * The default implementation of [[viper.carbon.modules.SeqModule]].
 */
class DefaultSeqModule(val verifier: Verifier) extends SeqModule {

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

  override def preamble = {
    if (used) {
      LiteralDecl(SequenceAxiomatization.value)
    } else {
      Nil
    }
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
        elems match {
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
      case sil.SeqUpdate(seq, idx, elem) =>
        FuncApp(Identifier("Seq#Update"), List(t(seq), t(idx), t(elem)), typ)
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
}
