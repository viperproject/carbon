package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie.{Type, Exp}

/**
 * A module for translating sets and multisets.
 *
 * @author Stefan Heule
 */
trait SetModule extends Module {
  def translateSetExp(exp: sil.Exp): Exp
  def translateSetType(setType: sil.SetType): Type
  def translateMultisetType(setType: sil.MultisetType): Type
}
