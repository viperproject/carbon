package semper.carbon.modules.impls

import semper.carbon.modules.SeqModule
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier

/**
 * The default implementation of [[semper.carbon.modules.SeqModule]].
 *
 * @author Stefan Heule
 */
class DefaultSeqModule(val verifier: Verifier) extends SeqModule {

  def name = "Sequence module"

  implicit val namespace = verifier.freshNamespace("seq")

  override def translateSeqExp(e: sil.Exp): Exp = {
    e match {
      case sil.EmptySeq(elemTyp) =>
      case sil.ExplicitSeq(elems) =>
      case sil.RangeSeq(low, high) =>
      case sil.SeqAppend(left, right) =>
      case sil.SeqElement(seq, idx) =>
      case sil.SeqTake(seq, n) =>
      case sil.SeqDrop(seq, n) =>
      case sil.SeqContains(elem, seq) =>
      case sil.SeqUpdate(seq, idx, elem) =>
      case sil.SeqLength(seq) =>
      case _ => sys.error("not a sequence expression")
    }
    ???
  }

  override def translateSeqType(seqType: sil.SeqType): Type = ???
}
