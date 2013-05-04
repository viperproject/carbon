package semper.carbon

import semper.sil.testing.DefaultSilSuite
import semper.sil.verifier.Verifier
import semper.sil.frontend.Frontend
import java.io.File
import io.Source
import java.nio.file.Path

/** All tests for carbon.
  *
  * @author Stefan Heule
  */
class AllTests extends DefaultSilSuite {

  override def testDirectories: Seq[String] = Vector("all")

  override def frontend(verifier: Verifier, files: Seq[Path]): Frontend = {
    require(files.length == 1, "tests should consist of exactly one file")
    val fe = new CarbonFrontend()
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  override def verifiers: Seq[Verifier] = Vector(CarbonVerifier())
}
