// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon

import boogie.{BoogieModelTransformer, Namespace, PrettyPrinter}
import modules.impls._
import viper.silver.ast.{MagicWand, Program, Quasihavoc, Quasihavocall}
import viper.silver.utility.Paths
import viper.silver.verifier._
import verifier.{BoogieDependency, BoogieInterface, Verifier}

import java.io.{BufferedOutputStream, File, FileOutputStream, IOException}
import viper.silver.frontend.{MissingDependencyException, NativeModel, VariablesModel}
import viper.silver.reporter.Reporter
import viper.silver.testing.BenchmarkStatCollector

/**
 * The main class to perform verification of Viper programs.  Deals with command-line arguments, configuration
 * of modules and choosing which module implementations to use.
 *
 * Debug information can either be set using the constructor argument or the setter.
 */
case class CarbonVerifier(override val reporter: Reporter,
                          private var _debugInfo: Seq[(String, Any)] = Nil) extends Verifier with viper.silver.verifier.Verifier with BoogieInterface {

  var env = null

  private var _config: CarbonConfig = _
  def config = _config

  def start(): Unit = {}
  def stop(): Unit = {
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

  var _stmtModule = new DefaultStmtModule(this)
  def stmtModule = _stmtModule
  var _expModule = new DefaultExpModule(this)
  def expModule = _expModule
  var _typeModule = new DefaultTypeModule(this)
  def typeModule = _typeModule
  var _exhaleModule = new DefaultExhaleModule(this)
  def exhaleModule = _exhaleModule
  var _inhaleModule = new DefaultInhaleModule(this)
  def inhaleModule = _inhaleModule
  var _heapModule = new DefaultHeapModule(this)
  def heapModule = _heapModule
  var _funcPredModule = new DefaultFuncPredModule(this)
  def funcPredModule = _funcPredModule
  var _permModule = new QuantifiedPermModule(this)
  def permModule = _permModule
  var _mainModule = new DefaultMainModule(this)
  def mainModule = _mainModule
  var _stateModule = new DefaultStateModule(this)
  def stateModule = _stateModule
  var _domainModule = new DefaultDomainModule(this)
  def domainModule = _domainModule
  var _seqModule = new DefaultSeqModule(this)
  def seqModule = _seqModule
  var _setModule = new DefaultSetModule(this)
  def setModule = _setModule
  var _mapModule = new DefaultMapModule(this)
  def mapModule = _mapModule
  var _wandModule = new DefaultWandModule(this)
  def wandModule = _wandModule
  var _loopModule = new DefaultLoopModule(this)
  def loopModule = _loopModule

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

  def assumeInjectivityOnInhale = if (config != null) config.assumeInjectivityOnInhale.toOption match {
    case Some(b) => b
    case None => false
  }
  else false

  override def usePolyMapsInEncoding =
    if (config != null) {
      config.desugarPolymorphicMaps.toOption match {
        case Some(b) => !b
        case None => true
      }
    } else {
      true
    }

  def name: String = "carbon"
  def version: String = "1.0"
  def buildVersion = version
  def copyright: String = "(c) 2013 ETH Zurich"

  def getDebugInfo = _debugInfo
  def debugInfo(info: Seq[(String, Any)]): Unit = {
    _debugInfo = info
  }

  def toolDesc = s"$name $version"
  def dependencyDescs = {
    (dependencies map (dep => {
      s"${dep.name} ${dep.version}, located at ${dep.location}."
    }))
  }

  def parseCommandLine(options: Seq[String]): Unit = {
    _config = new CarbonConfig(options)
  }

  lazy val dependencies: Seq[Dependency] = {
    import scala.sys.process._
    val unknownVersion = "(?)"
    List(new BoogieDependency(boogiePath), new Dependency {
      def name = "Z3"
      def version = {
        try {
          val v = List(z3Path, "-version").lazyLines.to(List)
          if (v.size == 1 && v(0).startsWith("Z3 version ")) {
            v(0).substring("Z3 version ".size)
          } else {
            unknownVersion
          }
        }
        catch {
          case _: IOException => throw MissingDependencyException("Z3 couldn't be found.")
        }

      }
      def location = z3Path
    })
  }

  def replaceAndStartAllModules() = {
    namespaceId = 0
    PrettyPrinter.reset()

    _stmtModule = new DefaultStmtModule(this)
    _expModule = new DefaultExpModule(this)
    _typeModule = new DefaultTypeModule(this)
    _exhaleModule = new DefaultExhaleModule(this)
    _inhaleModule = new DefaultInhaleModule(this)
    _heapModule = new DefaultHeapModule(this)
    _funcPredModule = new DefaultFuncPredModule(this)
    _permModule = new QuantifiedPermModule(this)
    _mainModule = new DefaultMainModule(this)
    _stateModule = new DefaultStateModule(this)
    _domainModule = new DefaultDomainModule(this)
    _seqModule = new DefaultSeqModule(this)
    _setModule = new DefaultSetModule(this)
    _mapModule = new DefaultMapModule(this)
    _wandModule = new DefaultWandModule(this)
    _loopModule = new DefaultLoopModule(this)


    // initialize all modules
    allModules foreach (m => {
      m.start()
    })
  }

  def verify(program: Program) : VerificationResult = {
    _program = program

    replaceAndStartAllModules()

    BenchmarkStatCollector.addStat("boogieTime")

    val unsupportedFeatures : Seq[AbstractError] =
      program.shallowCollect(
        n =>
          n match {
            case q@Quasihavoc(_, MagicWand(_, _)) =>
              ConsistencyError("Carbon does not support quasihavoc of magic wands", q.pos)
          }
      )

    if(unsupportedFeatures.nonEmpty) {
      return Failure(unsupportedFeatures)
    }

    // reset all modules
    allModules map (m => m.reset())
    heapModule.enableAllocationEncoding = config == null || !config.disableAllocEncoding.isSupplied // NOTE: config == null happens on the build server / via sbt test

    var transformNames = false
    if (config == null) Seq() else config.counterexample.toOption match {
      case Some(NativeModel) =>
      case Some(VariablesModel) => transformNames = true
      case None =>
      case Some(v) => sys.error("Invalid option: " + v)
    }

    val (tProg, translatedNames) = mainModule.translate(program, reporter)
    _translated = tProg


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
        }) ++
          (config.counterexample.toOption match {
            case Some(_) => {
              /* [2020-05-31 Marco] We use /mv:- instead of /printModel:1 because Boogie, at least the versions I tried,
               * does not properly separate models for different errors when it prints multiple ones and uses multiple
               * threads. I.e., it ill mix lines belonging to different models, which makes them useless.
               */
              List("/mv:-")
            }
            case _ => Nil
          })
      }
    }

    var timeout: Option[Int] = None

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
      timeout = config.timeout.toOption
    }

    val randomize = if (config == null) false else config.proverRandomizeSeeds.toOption match {
      case Some(b) => b
      case None => false
    }
    val randomSeed = if (config == null) None else config.proverSpecificRandomSeed.toOption

    invokeBoogie(_translated, options, timeout, randomize, randomSeed) match {
      case (version,result) =>
        if (version!=null) { dependencies.foreach(_ match {
          case b:BoogieDependency => b.version = version
          case _ => }) }

        result match {
          case Failure(errors) if transformNames => {
            errors.foreach(e =>  BoogieModelTransformer.transformCounterexample(e, translatedNames))
          }
          case _ => result
        }
        result
    }
  }



  private var _translated: viper.carbon.boogie.Program = null
  def translated = _translated

  private var _program: Program = null
  def program = _program
  def program_=(p : Program): Unit = {
    _program = p
  }

  def replaceProgram(prog : Program) = {this.program = prog}
}
