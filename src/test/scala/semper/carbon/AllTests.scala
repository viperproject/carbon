package semper.carbon

import semper.sil.testing.DefaultSilSuite
import semper.sil.verifier.Verifier
import semper.sil.frontend.Frontend

/** All tests for carbon.
  *
  * @author Stefan Heule
  */
class AllTests extends DefaultSilSuite {

  override def testDirectories: Seq[String] = Vector("basic")

  override def frontend(verifier: Verifier, input: String): Frontend = {
    val fe = new CarbonFrontend()
    fe.init(verifier)
    fe.reset(input)
    fe
  }

  override def verifiers: Seq[Verifier] = Vector(CarbonVerifier())
}
