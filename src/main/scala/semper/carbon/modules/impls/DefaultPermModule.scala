package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.boogie._

/**
 * The default implementation of a [[semper.carbon.modules.PermModule]].
 *
 * @author Stefan Heule
 */
class DefaultPermModule(val verifier: Verifier) extends PermModule {
  def name = "Permission module"
}
