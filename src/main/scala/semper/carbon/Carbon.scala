package semper.carbon

import semper.sil.frontend.{SilFrontend, SilFrontendConfig}

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
  private var carbonInstance: CarbonVerifier = _

  def createVerifier(fullCmd: String) = {
    carbonInstance = CarbonVerifier(Seq("Arguments: " -> fullCmd))

    carbonInstance
  }

  def configureVerifier(args: Seq[String]) = {
  	carbonInstance.parseCommandLine(args)

    carbonInstance.config
  }
}

class CarbonConfig(args: Seq[String]) extends SilFrontendConfig(args, "Carbon") {
  val boogieProverLog = opt[String]("proverLog",
    descr = "Prover log file written by Boogie (default: none)",
    default = None,
    noshort = true
  )
}
