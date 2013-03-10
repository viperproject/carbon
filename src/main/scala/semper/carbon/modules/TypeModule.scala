package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie.Type

/**
 * A module for translating types.
 *
 * @author Stefan Heule
 */
trait TypeModule extends Module with AllModule {
  def translateType(typ: sil.Type): Type
}
