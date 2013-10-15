package semper.carbon

import semper.sil.frontend.{SilFrontend, SilFrontendConfig}
import semper.sil.verifier.Verifier

/**
 * The main object for Carbon containing the execution start-point.
 *
 * @author Stefan Heule
 */
object Carbon extends CarbonFrontend {

  def main(args: Array[String]) {
    execute(args)
  }


}

class CarbonFrontend extends SilFrontend {
  def createVerifier(fullCmd: String) = CarbonVerifier(Seq("Arguments: " -> fullCmd))
  def configureVerifier(args: Seq[String]) = {
  	new SilFrontendConfig(args, "Carbon")
  }
}