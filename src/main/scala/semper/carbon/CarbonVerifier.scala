package semper.carbon

import modules.impls._
import modules.Verifier
import semper._
import sil.ast.Program
import sil.utility.Paths
import sil.verifier.Dependency

/**
 * The main class to perform verification of SIL programs.  Deals with command-line arguments, configuration
 * of modules and choosing which module implementations to use.
 *
 * @author Stefan Heule
 */
case class CarbonVerifier(fullCmd: String) extends Verifier with sil.verifier.Verifier {

  def stmtModule = new DefaultStmtModule(this)
  def expModule = new DefaultExpModule(this)
  def typeModule = new DefaultTypeModule(this)
  def exhaleModule = new DefaultExhaleModule(this)
  def inhaleModule = new DefaultInhaleModule(this)
  def heapModule = new DefaultHeapModule(this)
  def funcPredModule = new DefaultFuncPredModule(this)
  def permModule = new DefaultPermModule(this)
  def mainModule = new DefaultMainModule(this)

  /** The (unresolved) path where Boogie is supposed to be located. */
  var _boogiePath: String = "${BOOGIE_EXE}"

  /** The (unresolved) path where Z3 is supposed to be located. */
  var _z3Path: String = "${Z3_EXE}"

  /** The (resolved) path where Boogie is supposed to be located. */
  def boogiePath = Paths.resolveEnvVars(_boogiePath)

  /** The (resolved) path where Z3 is supposed to be located. */
  def z3Path = Paths.resolveEnvVars(_z3Path)

  def name: String = "carbon"
  def version: String = "1.0"
  def copyright: String = "(c) 2013 Stefan Heule"

  def toolDesc = s"$name $version"

  def commandLineArgs(options: Seq[String]) {}

  lazy val dependencies: Seq[Dependency] = {
    import scala.sys.process._
    val unknownVersion = "(?)"
    List(new Dependency {
      def name = "Boogie"
      def version = {
        def convertStreamToString(is: java.io.InputStream) = {
          val s = new java.util.Scanner(is).useDelimiter("\\A")
          if (s.hasNext) s.next() else ""
        }
        var res: String = ""
        def out(input: java.io.InputStream) {
          res = convertStreamToString(input)
          input.close()
        }
        // Note: call exitValue to block until Boogie has finished
        // Note: we call boogie with an empty input "file" on stdin and parse the output
        Seq(boogiePath, "stdin.bpl").run(new ProcessIO(_.close(), out, _.close())).exitValue()
        if (res.startsWith("Boogie program modules version ")) {
          res.substring(0, res.indexOf(",")).substring("Boogie program modules version ".length)
        } else {
          unknownVersion
        }
      }
      def location = boogiePath
    }, new Dependency {
      def name = "Z3"
      def version = {
        val v = List(z3Path, "/version").lines.to[List]
        if (v.size == 1 && v(0).startsWith("Z3 version ")) {
          v(0).substring("Z3 version ".size)
        } else {
          unknownVersion
        }
      }
      def location = z3Path
    })
  }

  def verify(program: Program) = ???
}
