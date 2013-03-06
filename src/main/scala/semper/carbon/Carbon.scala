package semper.carbon

import modules.CarbonVerifier
import semper.sil.frontend.SilFrontend
import semper.sil.verifier.Verifier

/**
 * The main object for Carbon containing the execution start-point.
 *
 * @author Stefan Heule
 */
object Carbon extends SilFrontend {

  def main(args: Array[String]) {
    execute(args)
  }

  def verifier: Verifier = CarbonVerifier()
}
