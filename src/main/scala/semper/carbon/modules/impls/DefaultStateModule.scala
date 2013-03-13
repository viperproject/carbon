package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.verifier.Verifier

/**
 * The default implementation of a [[semper.carbon.modules.StateModule]].
 *
 * @author Stefan Heule
 */
class DefaultStateModule(val verifier: Verifier) extends StateModule {
  def name = "State module"
}
