package semper.carbon.modules.impls

import semper.carbon.modules.SeqModule
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier
import semper.carbon.boogie.Implicits._

/**
 * The default implementation of [[semper.carbon.modules.SeqModule]].
 *
 * @author Stefan Heule
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
        FuncApp(Identifier("Seq#Empty"), Nil, typ)
      case sil.ExplicitSeq(elems) =>
        def buildSeq(es: Seq[sil.Exp]): Exp = {
          elems match {
            case Nil => sys.error("did not expect empty sequence")
            case a :: Nil =>
              FuncApp(Identifier("Seq#Singleton"), t(a), typ)
            case a :: as =>
              val aTranslated = FuncApp(Identifier("Seq#Singleton"), t(a), typ)
              FuncApp(Identifier("Seq#Append"), List(aTranslated, buildSeq(as)), typ)
          }
        }
        buildSeq(elems)
      case sil.RangeSeq(low, high) =>
        FuncApp(Identifier("Seq#Range"), List(t(low), t(high)), typ)
      case sil.SeqAppend(left, right) =>
        FuncApp(Identifier("Seq#Append"), List(t(left), t(right)), typ)
      case sil.SeqElement(seq, idx) =>
        FuncApp(Identifier("Seq#Index"), List(t(seq), t(idx)), typ)
      case sil.SeqTake(seq, n) =>
        FuncApp(Identifier("Seq#Take"), List(t(seq), t(n)), typ)
      case sil.SeqDrop(seq, n) =>
        FuncApp(Identifier("Seq#Drop"), List(t(seq), t(n)), typ)
      case sil.SeqContains(elem, seq) =>
        FuncApp(Identifier("Seq#Index"), List(t(seq), t(elem)), typ)
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
