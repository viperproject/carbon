package semper.carbon.modules

import semper.sil.{ast => sil}

/**
 * Common trait for modules.
 *
 * @author Stefan Heule
 */
trait Module {
  /** The verifier to interact with other modules. */
  def verifier: Verifier
}
