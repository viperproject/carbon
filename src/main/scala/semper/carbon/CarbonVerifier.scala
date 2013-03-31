package semper.carbon

import boogie.Namespace
import modules.impls._
import semper._
import sil.ast.Program
import sil.utility.Paths
import sil.verifier.Dependency
import verifier.{BoogieInterface, Verifier}
import java.io.File

/**
 * The main class to perform verification of SIL programs.  Deals with command-line arguments, configuration
 * of modules and choosing which module implementations to use.
 *
 * Debug information can either be set using the constructor argument or the setter.
 *
 * @author Stefan Heule
 */
case class CarbonVerifier(private var _debugInfo: Seq[(String, Any)] = Nil) extends Verifier with sil.verifier.Verifier with BoogieInterface {

  var env = null

  private var namespaceId = 0
  override def freshNamespace(name: String): Namespace = {
    namespaceId += 1
    Namespace(name, namespaceId)
  }

  val stmtModule = new DefaultStmtModule(this)
  val expModule = new DefaultExpModule(this)
  val typeModule = new DefaultTypeModule(this)
  val exhaleModule = new DefaultExhaleModule(this)
  val inhaleModule = new DefaultInhaleModule(this)
  val heapModule = new DefaultHeapModule(this)
  val funcPredModule = new DefaultFuncPredModule(this)
  val permModule = new DefaultPermModule(this)
  val mainModule = new DefaultMainModule(this)
  val stateModule = new DefaultStateModule(this)
  val domainModule = new DefaultDomainModule(this)

  // initialize all modules
  allModules foreach (m => {
    m.initialize()
  })

  /** The (unresolved) path where Boogie is supposed to be located. */
  var _boogiePath: String = "${BOOGIE_EXE}"

  /** The (unresolved) path where Z3 is supposed to be located. */
  var _z3Path: String = "${Z3_EXE}"

  /** The (resolved) path where Boogie is supposed to be located. */
  def boogiePath = new File(Paths.resolveEnvVars(_boogiePath)).getAbsolutePath

  /** The (resolved) path where Z3 is supposed to be located. */
  def z3Path = new File(Paths.resolveEnvVars(_z3Path)).getAbsolutePath

  def name: String = "carbon"
  def version: String = "1.0"
  def buildVersion = version
  def copyright: String = "(c) 2013 Stefan Heule"

  def getDebugInfo = _debugInfo
  def debugInfo(info: Seq[(String, Any)]) {
    _debugInfo = info
  }

  def toolDesc = s"$name $version"
  def dependencyDescs = {
    (dependencies map (dep => {
      s"${dep.name} ${dep.version}, located at ${dep.location}."
    }))
  }

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
        if (res.startsWith("Boogie program verifier version ")) {
          res.substring(0, res.indexOf(",")).substring("Boogie program verifier version ".length)
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

  def verify(program: Program) = {
    _translated = mainModule.translate(program)
    invokeBoogie(_translated, Nil)
  }

  private var _translated: semper.carbon.boogie.Program = null
  def translated = _translated
}
