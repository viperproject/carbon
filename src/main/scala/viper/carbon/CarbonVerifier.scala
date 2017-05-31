/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon

import boogie.Namespace
import modules.impls._
import viper._
import viper.silver.ast.{Program,Method}
import viper.silver.components.StatefulComponent
import viper.silver.utility.Paths
import viper.silver.verifier.Dependency
import verifier.{BoogieInterface, Verifier, BoogieDependency}
import java.io.{FileOutputStream, BufferedOutputStream, File}



/**
 * The main class to perform verification of Viper programs.  Deals with command-line arguments, configuration
 * of modules and choosing which module implementations to use.
 *
 * Debug information can either be set using the constructor argument or the setter.
 */
case class CarbonVerifier(private var _debugInfo: Seq[(String, Any)] = Nil) extends Verifier with viper.silver.verifier.Verifier with BoogieInterface {

  def this() = this(Nil)

  var env = null

  private var _config: CarbonConfig = _
  def config = _config

  def start() = {}
  def stop() {
    if (allModules != null) {
      allModules foreach (m => {
        m.stop()
      })
    }
    stopBoogie()
  }

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
  val permModule = new QuantifiedPermModule(this)
  val mainModule = new DefaultMainModule(this)
  val stateModule = new DefaultStateModule(this)
  val domainModule = new DefaultDomainModule(this)
  val seqModule = new DefaultSeqModule(this)
  val setModule = new DefaultSetModule(this)
  val wandModule = new DefaultWandModule(this)

  // initialize all modules
  allModules foreach (m => {
    m.start()
  })

  /** The default location for Boogie (the environment variable ${BOOGIE_EXE}). */
  lazy val boogieDefault: String = new File(Paths.resolveEnvVars("${BOOGIE_EXE}")).getAbsolutePath

  /** The default location for Z3 (the environment variable ${Z3_EXE}). */
  lazy val z3Default: String = new File(Paths.resolveEnvVars("${Z3_EXE}")).getAbsolutePath

  /** The (resolved) path where Boogie is supposed to be located. */

  def boogiePath = if (config != null) config.boogieExecutable.toOption match {
    case Some(path) => new File(path).getAbsolutePath
    case None => boogieDefault
  } else boogieDefault

  /** The (resolved) path where Z3 is supposed to be located. */
  def z3Path = if (config != null) config.Z3executable.toOption match {
    case Some(path) => {new File(path).getAbsolutePath}
    case None => z3Default
  } else z3Default

  def name: String = "carbon"
  def version: String = "1.0"
  def buildVersion = version
  def copyright: String = "(c) 2013 ETH Zurich"

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

  def parseCommandLine(options: Seq[String]) {
    _config = new CarbonConfig(options)
  }

  lazy val dependencies: Seq[Dependency] = {
    import scala.sys.process._
    val unknownVersion = "(?)"
    List(new BoogieDependency(boogiePath), new Dependency {
      def name = "Z3"
      def version = {
        val v = List(z3Path, "-version").lines.to[List]
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
    _program = program

    // reset all modules
    allModules map (m => m.reset())

    _translated = mainModule.translate(program)

    val options = {
      if (config == null) {
        Nil
      } else {
        (config.boogieProverLog.toOption match {
      case Some(l) =>
        List("/proverLog:" + l + " ")
      case None =>
        Nil
      }) ++
        (config.boogieOpt.toOption match {
          case Some(l) =>
            l.split(" ")
          case None =>
            Nil
        })
      }
    }

    if(config != null)
    {
      config.boogieOut.toOption match {
        case Some(filename) =>
          // write Boogie program to the specified file
          val f = new File(filename)
          val stream = new BufferedOutputStream(new FileOutputStream(f))
          stream.write(_translated.toString.getBytes)
          stream.close()
        case None =>
      }
    }

    invokeBoogie(_translated, options) match {
      case (version,result) =>
        if (version!=null) { dependencies.foreach(_ match {
          case b:BoogieDependency => b.version = version
          case _ => }) }
        result
    }
  }

  private var _translated: viper.carbon.boogie.Program = null
  def translated = _translated

  private var _program: Program = null
  def program = _program
  def program_=(p : Program) {
    _program = p
  }

  def replaceProgram(prog : Program) = {this.program = prog}
}
