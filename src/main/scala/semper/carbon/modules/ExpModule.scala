package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie.Exp

/**
 * A module to translate SIL statements.
 *
 * @author Stefan Heule
 */
trait ExpModule extends Module with AllModule {
  def translateExp(exp: sil.Exp): Exp
}
