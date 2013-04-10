package semper.carbon.modules

import semper.carbon.boogie._
import semper.sil.{ast => sil}

/**
 * The permission module determines the encoding of permissions and allows to add or remove
 * permission.
 *
 * @author Stefan Heule
 */
trait PermModule extends Module {

  /**
   * The type used to represent permissions.
   */
  def permType: Type

  /**
   * Translate a permission amount
   */
  def translatePerm(e: sil.Exp): Exp
}
