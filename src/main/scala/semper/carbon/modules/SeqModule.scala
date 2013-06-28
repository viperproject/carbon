package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie.{Type, Exp}

/**
 * A module for translating sequences.
 *
 * @author Stefan Heule
 */
trait SeqModule extends Module {
  def translateSeqExp(exp: sil.Exp): Exp
  def translateSeqType(seqType: sil.SeqType): Type
}
