package viper.carbon

import java.nio.file.Path

import org.scalatest.DoNotDiscover

import viper.silver.frontend.Frontend
import viper.silver.logger.SilentLogger
import viper.silver.reporter.NoopReporter
import viper.silver.testing.SilSuite
import viper.silver.verifier.Verifier

/**
  * Currently, we do not run the graph tests by default. This could be easily changed later by removing the
  * [[DoNotDiscover]] annotation.
  */
@DoNotDiscover
class GraphTests extends SilSuite {
  override def testDirectories: Seq[String] = Vector("graphs")

  override def frontend(verifier: Verifier, files: Seq[Path]): Frontend = {
    require(files.length == 1, "tests should consist of exactly one file")
    val fe = new CarbonFrontend(NoopReporter, SilentLogger().get)
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  lazy val verifiers = List(CarbonVerifier())
}
