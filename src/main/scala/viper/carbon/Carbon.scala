// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon

import ch.qos.logback.classic.Logger
import viper.silver.frontend.{MinimalViperFrontendAPI, SilFrontend, SilFrontendConfig, ViperFrontendAPI}
import viper.silver.logger.ViperStdOutLogger
import viper.silver.reporter.{Reporter, StdIOReporter}
import viper.silver.verifier.{Verifier => SilVerifier}

/**
 * The main object for Carbon containing the execution start-point.
 */
object Carbon extends CarbonFrontend(StdIOReporter("carbon_reporter"), ViperStdOutLogger("Carbon", "INFO").get) {
  def main(args: Array[String]): Unit = {
    execute(args)
    specifyAppExitCode()
    sys.exit(appExitCode)
  }
}

class CarbonFrontend(override val reporter: Reporter,
                     override val logger: Logger) extends SilFrontend {

  private var carbonInstance: CarbonVerifier = _

  override def backendTypeFormat: Option[String] = Some("Boogie")

  def createVerifier(fullCmd: String) = {
    carbonInstance = CarbonVerifier(reporter, Seq("Arguments: " -> fullCmd))

    carbonInstance
  }

  def configureVerifier(args: Seq[String]) = {
  	carbonInstance.parseCommandLine(args)

    carbonInstance.config
  }

  override def init(verifier: SilVerifier): Unit = {
    verifier match {
      case carbon: CarbonVerifier =>
        carbonInstance = carbon
      case _ =>
        sys.error( "Expected verifier to be an instance of CarbonVerifier but got an instance " +
                  s"of ${verifier.getClass}")
    }

    super.init(verifier)

    _config = carbonInstance.config
  }
}

/**
  * Carbon "frontend" for use by actual Viper frontends.
  * Performs consistency check and verification.
  * See [[viper.silver.frontend.ViperFrontendAPI]] for usage information.
  */
class CarbonFrontendAPI(override val reporter: Reporter)
  extends CarbonFrontend(reporter, ViperStdOutLogger("CarbonFrontend", "INFO").get) with ViperFrontendAPI

/**
  * Carbon "frontend" for use by actual Viper frontends.
  * Performs only verification (no consistency check).
  * See [[viper.silver.frontend.ViperFrontendAPI]] for usage information.
  */
class MinimalCarbonFrontendAPI(override val reporter: Reporter)
  extends CarbonFrontend(reporter, ViperStdOutLogger("CarbonFrontend", "INFO").get) with MinimalViperFrontendAPI

class CarbonConfig(args: Seq[String]) extends SilFrontendConfig(args, "Carbon") {
  val boogieProverLog = opt[String]("proverLog",
    descr = "Prover log file written by Boogie (default: none)",
    default = None,
    noshort = true
  )

  val boogieOut = opt[String]("print",
    descr = "Write the Boogie output file to the provided filename (default: none)",
    default = None,
    noshort = true
  )

  val boogieOpt = opt[String]("boogieOpt",
  descr = "Option(s) to pass-through as options to Boogie (changing the output generated by Boogie is not supported) (default: none)",
  default = None,
  noshort = true
  )

  val boogieExecutable = opt[String]("boogieExe",
    descr = "Manually-specified full path to Boogie.exe executable (default: ${BOOGIE_EXE})",
    default = None,
    noshort = true
  )

  val Z3executable = opt[String]("z3Exe",
    descr = "Manually-specified full path to Z3.exe executable (default: ${Z3_EXE})",
    default = None,
    noshort = true
  )

  val disableAllocEncoding = opt[Boolean]("disableAllocEncoding",
    descr = "Disable Allocation-related assumptions (default: enabled)",
    default = None,
    noshort = true
  )

  val desugarPolymorphicMaps = opt[Boolean]("desugarPolymorphicMaps",
    descr = "Do not use polymorphic maps in the Boogie encoding and instead desugar them (default: false).",
    default = Some(false),
    noshort = true
  )

  val timeout = opt[Int]("timeout",
    descr = ("Time out after approx. n seconds. The timeout is for the whole verification in Boogie, "
           + "not per method or proof obligation (default: 0, i.e. no timeout)."),
    default = None,
    noshort = true
  )

  verify()
}
