package semper.carbon

import semper.sil.frontend.SilFrontEnd
import semper.sil.verifier.{VerificationResult, Verifier}
import semper.sil.ast.Program

/**
 * The main object for Carbon containing the execution start-point.
 *
 * @author Stefan Heule
 */
object Carbon extends SilFrontEnd {

  def main(args: Array[String]) {
    execute(args)
  }

  def verifier: Verifier = new Verifier() {
    def verify(program: Program): VerificationResult = null
    def name = "carbon"
    def dependencyVersions = Nil
    def version = "1.0"
    def copyright = "(c) 2013 Stefan Heule"
    def commandLineArgs(options: Seq[String]) {

    }
  }
}
