// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.verifier

import viper.carbon.boogie.{Assert, Program}
import viper.silver.reporter.BackendSubProcessStages._
import viper.silver.reporter.{BackendSubProcessReport, Reporter}
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.reasons.InternalReason
import viper.silver.verifier._

import java.io._
import scala.jdk.CollectionConverters._

class BoogieDependency(_location: String) extends Dependency {
  def name = "Boogie"
  def location = _location
  var version = "" // filled-in when Boogie is invoked
}

class InputStreamConsumer(val is: InputStream, actionBeforeConsumption: () => Unit) extends Runnable {
  var result : Option[String] = None

  private def convertStreamToString(is: InputStream) = {
    val s = new java.util.Scanner(is).useDelimiter("\\A")
    if (s.hasNext) s.next() else ""
  }

  def run(): Unit = {
    actionBeforeConsumption()
    result = Some(convertStreamToString(is))
    is.close()
  }
}

case class FailureContextImpl(counterExample: Option[Counterexample]) extends FailureContext

/**
  * Defines a clean interface to invoke Boogie and get a list of errors back.
  */

trait BoogieInterface {

  def reporter: Reporter

  def defaultOptions = Seq("/vcsCores:" + java.lang.Runtime.getRuntime.availableProcessors,
    "/errorTrace:0",
    "/errorLimit:10000000",
    "/proverOpt:O:smt.AUTO_CONFIG=false",
    "/proverOpt:O:smt.PHASE_SELECTION=0",
    "/proverOpt:O:smt.RESTART_STRATEGY=0",
    "/proverOpt:O:smt.RESTART_FACTOR=|1.5|",
    "/proverOpt:O:smt.ARITH.RANDOM_INITIAL_VALUE=true",
    "/proverOpt:O:smt.CASE_SPLIT=3",
    "/proverOpt:O:smt.DELAY_UNITS=true",
    "/proverOpt:O:NNF.SK_HACK=true",
    "/proverOpt:O:smt.MBQI=false",
    "/proverOpt:O:smt.QI.EAGER_THRESHOLD=100",
    "/proverOpt:O:smt.BV.REFLECT=true",
    "/proverOpt:O:smt.qi.max_multi_patterns=1000",
    s"/proverOpt:PROVER_PATH=$z3Path")

  /** The (resolved) path where Boogie is supposed to be located. */
  def boogiePath: String

  /** The (resolved) path where Z3 is supposed to be located. */
  def z3Path: String

  private var _boogieProcess: Option[Process] = None
  private var _boogieProcessPid: Option[Long] = None

  // Z3 processes cannot be collected this way, perhaps because they are not created using Java 9 API (but via Boogie).
  // Hence, for now we have to trust Boogie to manage its own sub-processes.
  // private var _z3ProcessStream: Option[LazyList[ProcessHandle]] = None

  var errormap: Map[Int, VerificationError] = Map()
  var models : collection.mutable.ListBuffer[String] = new collection.mutable.ListBuffer[String]
  def invokeBoogie(program: Program, options: Seq[String]): (String,VerificationResult) = {
    // find all errors and assign everyone a unique id
    errormap = Map()
    program.visit {
      case a@Assert(exp, error) =>
        errormap += (a.id -> error)
    }

    // invoke Boogie
    val output = run(program.toString, defaultOptions ++ options)

    // parse the output
    parse(output) match {
      case (version,Nil) =>
        (version,Success)
      case (version,errorIds) => {
        val errors = (0 until errorIds.length).map(i => {
          val id = errorIds(i)
          val error = errormap.get(id).get
          if (models.nonEmpty)
            error.failureContexts = Seq(FailureContextImpl(Some(SimpleCounterexample(Model(models(i))))))
          error
        })
        (version,Failure(errors))
      }
    }
  }

  /**
    * Parse the output of Boogie. Returns a pair of the detected version number and a sequence of error identifiers.
    */
  private def parse(output: String): (String,Seq[Int]) = {
    val LogoPattern = "Boogie program verifier version ([0-9.]+),.*".r
    val SummaryPattern = "Boogie program verifier finished with ([0-9]+) verified, ([0-9]+) error.*".r
    val ErrorPattern = "  .+ \\[([0-9]+)\\]".r
    val errors = collection.mutable.ListBuffer[Int]()
    var otherErrId = 0
    var version_found : String = null

    val unexpected : (String => Unit) = (msg:String) => {
      otherErrId -= 1
      errors += otherErrId
      val internalError = Internal(InternalReason(DummyNode, msg))
      errormap += (otherErrId -> internalError)
    }

    var parsingModel : Option[StringBuilder] = None
    var stateInitialBlock = false
    for (l <- output.linesIterator) {
      l match {
        case "*** END_STATE" =>
          stateInitialBlock = false
        case "*** STATE <initial>" =>
          stateInitialBlock = true
        case _ if stateInitialBlock => //ignore everything within state block
        case "*** END_MODEL" if parsingModel.isDefined =>
          models.append(parsingModel.get.toString())
          parsingModel = None
        case _ if parsingModel.isDefined =>
          parsingModel.get.append(l).append("\n")
        case "*** MODEL" if parsingModel.isEmpty =>
          parsingModel = Some(new StringBuilder)
        case LogoPattern(version) =>
          version_found = version
        case ErrorPattern(id) =>
          errors += id.toInt
        case SummaryPattern(v, e) =>
          if(e.toInt != errors.size) unexpected(s"Found ${errors.size} errors, but there should be $e. The output was: $output")
        case "" => // ignore empty lines
        case _ =>
          unexpected(s"Found an unparsable output from Boogie: $l")
      }
    }
    (version_found,errors.toSeq)
  }

  /**
    * Invoke Boogie.
    */
  private def run(input: String, options: Seq[String]) = {
    reporter report BackendSubProcessReport("carbon", boogiePath, BeforeInputSent, _boogieProcessPid)

    // When the filename is "stdin.bpl" Boogie reads the program from standard input.
    val cmd: Seq[String] = Seq(boogiePath) ++ options ++ Seq("stdin.bpl")
    val pb: ProcessBuilder = new ProcessBuilder(cmd.asJava)
    val proc: Process = pb.start()
    _boogieProcess = Some(proc)
    _boogieProcessPid = Some(proc.pid)

    //proverShutDownHook approach taken from Silicon's codebase
    val proverShutdownHook = new Thread {
      override def run(): Unit = {
        destroyProcessAndItsChildren(proc, boogiePath)
      }
    }
    Runtime.getRuntime.addShutdownHook(proverShutdownHook)

    // _z3ProcessStream = Some(proc.descendants().toScala(LazyList))
    reporter report BackendSubProcessReport("carbon", boogiePath, AfterInputSent, _boogieProcessPid)

    val errorConsumer =
      new InputStreamConsumer(proc.getErrorStream, () => reporter report BackendSubProcessReport("carbon", boogiePath, OnError, _boogieProcessPid))
    val errorStreamThread = new Thread(errorConsumer)
    val inputConsumer =
      new InputStreamConsumer(proc.getInputStream, () => reporter report BackendSubProcessReport("carbon", boogiePath, OnOutput, _boogieProcessPid))
    val inputStreamThread = new Thread(inputConsumer)

    errorStreamThread.start()
    inputStreamThread.start()

    // Send the program to Boogie
    proc.getOutputStream.write(input.getBytes);
    proc.getOutputStream.close()

    try {
      proc.waitFor()
    } finally {
      destroyProcessAndItsChildren(proc, boogiePath)
    }

    // Deregister the shutdown hook, otherwise the prover process that has been stopped cannot be garbage collected.
    // Explanation: https://blog.creekorful.org/2020/03/classloader-and-memory-leaks/
    // Bug report: https://github.com/viperproject/silicon/issues/579
    Runtime.getRuntime.removeShutdownHook(proverShutdownHook)

    errorStreamThread.join()
    inputStreamThread.join()

    try {
      val errorOutput = errorConsumer.result.get
      val normalOutput = inputConsumer.result.get
      reporter report BackendSubProcessReport("carbon", boogiePath, OnExit, _boogieProcessPid)

      errorOutput + normalOutput
    } catch {
      case _: NoSuchElementException => sys.error("Could not retrieve output from Boogie")
    }
  }

  private def destroyProcessAndItsChildren(proc: Process, processPath: String) : Unit = {
    if(proc.isAlive) {
      reporter report BackendSubProcessReport("carbon", processPath, BeforeTermination, _boogieProcessPid)
      proc.children().forEach(_.destroy() : Unit)
      proc.destroy()
      reporter report BackendSubProcessReport("carbon", processPath, AfterTermination, _boogieProcessPid)
    }
  }

  def stopBoogie(): Unit = {
    _boogieProcess match {
      case Some(proc) =>
        destroyProcessAndItsChildren(proc, boogiePath)
      case None =>
    }
  }
}
