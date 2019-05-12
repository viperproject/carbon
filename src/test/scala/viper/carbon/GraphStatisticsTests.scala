package viper.carbon

import java.nio.file.Path

import org.scalatest.DoNotDiscover
import viper.silver
import viper.silver.frontend.Frontend
import viper.silver.logger.SilentLogger
import viper.silver.reporter.NoopReporter
import viper.silver.testing._
import viper.silver.utility.TimingUtils
import viper.silver.verifier.Verifier

/**
  * Currently, we do not run the graph tests by default. This could be easily changed later by removing the
  * [[DoNotDiscover]] annotation.
  */
@DoNotDiscover
class GraphStatisticsTests extends SilSuite {

  val benchmark = true
  val numOfExecutions = 1

  val testDirectories: Seq[String] =
    if (benchmark) Vector(
      //"graphs/dynamic/warmup",
      "graphs/dynamic/examples")
    else Vector("graphs/dynamic/immutable")

//  override def testDirectories: Seq[String] =
//    Vector(
//      //"graphs/static",
//      "graphs/dynamic/immutable",
//      "graphs/dynamic/unary/utests",
//      //"graphs/dynamic/unary/examples",
//      "graphs/dynamic/binary/utests",
//      "graphs/dynamic/binary/examples",
//      "graphs/dynamic/ternary/utests",
//      //"graphs/dynamic/ternary/examples"
//    )

  override def frontend(verifier: Verifier, files: Seq[Path]): Frontend = {
    require(files.length == 1, "tests should consist of exactly one file")
    val fe = new CarbonFrontend(NoopReporter, SilentLogger().get)
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  val chuckwallaInstanceUnderTest: SystemUnderTest =
    new SystemUnderTest with TimingUtils {
      val projectInfo: ProjectInfo = new ProjectInfo(List("Carbon-Chuckwalla"))

      def run(input: AnnotatedTestInput): Seq[AbstractOutput] = {
        info(s"Say hello to Chuckwalla statistics!")
        val data = for (_ <- 1 to numOfExecutions) yield {
          val fe = frontend(chuckwallaVerifier, input.files)
          val tEntry = fe.phases.map { p =>
              time(p.action)._2
          }.mkString(", ")
          "\n" + tEntry
        }
        info(s"Time required: $data.")

        Vector.empty
      }
    }

  override def systemsUnderTest:Seq[silver.testing.SystemUnderTest] = Vector(chuckwallaInstanceUnderTest)

  val chuckwallaVerifier = CarbonVerifier()
  lazy val verifiers = List(chuckwallaVerifier)
}
