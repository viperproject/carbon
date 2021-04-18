// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.verifier

import java.io._

import viper.carbon.boogie.{Assert, Program}
import viper.silver.reporter.BackendSubProcessStages._
import viper.silver.reporter.{BackendSubProcessReport, Reporter}
import viper.silver.verifier.errors.Internal
import viper.silver.verifier.reasons.InternalReason
import viper.silver.verifier.{Failure, _}

import scala.jdk.CollectionConverters._
import scala.jdk.StreamConverters._



class BoogieDependency(_location: String) extends Dependency {
  def name = "Boogie"
  def location = _location
  var version = "" // filled-in when Boogie is invoked
}

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
  private var _z3ProcessStream: Option[LazyList[ProcessHandle]] = None

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
            error.counterexample = Some(SimpleCounterexample(Model(models(i))))
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
    for (l <- output.linesIterator) {
      l match {
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
  private def run(input: String, options: Seq[String]): String = {
    def convertStreamToString(is: java.io.InputStream) = {
      val s = new java.util.Scanner(is).useDelimiter("\\A")
      if (s.hasNext) s.next() else ""
    }
    var res: String = ""
    var reserr: String = ""
    def out(input: InputStream): Unit = {
      reporter report BackendSubProcessReport("carbon", boogiePath, onOutput, _boogieProcessPid)
      res += convertStreamToString(input)
      input.close()
    }
    def err(in: InputStream): Unit = {
      reporter report BackendSubProcessReport("carbon", boogiePath, OnError, _boogieProcessPid)
      reserr += convertStreamToString(in)
      in.close()
    }
    // write program to a temporary file
    val tmp = File.createTempFile("carbon", ".bpl")

    tmp.deleteOnExit()
    val stream = new BufferedOutputStream(new FileOutputStream(tmp))
    stream.write(input.getBytes)
    stream.close()

    reporter report BackendSubProcessReport("carbon", boogiePath, BeforeInputSent, _boogieProcessPid)

    val cmd: Seq[String] = (Seq(boogiePath) ++ options ++ Seq(tmp.getAbsolutePath))
    val pb: ProcessBuilder = new ProcessBuilder(cmd.asJava)
    val proc: Process = pb.start()
    _boogieProcess = Some(proc)
    _boogieProcessPid = Some(proc.pid)

    proc.getOutputStream.close()

    _z3ProcessStream = Some(proc.descendants().toScala(LazyList))
    reporter report BackendSubProcessReport("carbon", boogiePath, AfterInputSent, _boogieProcessPid)
    err(proc.getErrorStream)
    out(proc.getInputStream)
    proc.waitFor()

    reporter report BackendSubProcessReport("carbon", boogiePath, OnExit, _boogieProcessPid)
    reserr + res
  }

  def stopBoogie(): Unit = {
    _boogieProcess match {
      case Some(proc) =>
        reporter report BackendSubProcessReport("carbon", boogiePath, BeforeTermination, _boogieProcessPid)
        proc.destroy()
        _z3ProcessStream match {
          case Some(stream) =>
            stream.foreach((ph: ProcessHandle) => {
              ph.destroy()
            })
          case None =>
        }
      reporter report BackendSubProcessReport("carbon", boogiePath, AfterTermination, _boogieProcessPid)
      case None =>
    }
  }

  /*  // TODO: investigate why passing the program directly does not work
    private def runX(input: String, options: Seq[String]): String = {
      def convertStreamToString(is: java.io.InputStream) = {
        val s = new java.util.Scanner(is).useDelimiter("\\A")
        if (s.hasNext) s.next() else ""
      }
      var res: String = ""
      var reserr: String = ""
      def out(input: java.io.InputStream) {
        res += convertStreamToString(input)
        input.close()
      }
      def err(in: java.io.InputStream) {
        reserr += convertStreamToString(in)
        in.close()
      }
      def in(output: java.io.OutputStream) {
        output.write(input.getBytes)
        output.close()
      }
      // Note: call exitValue to block until Boogie has finished
      // Note: we call boogie with an empty input "file" on stdin and parse the output
      (Seq(boogiePath) ++ options ++ Seq("stdin.bpl")).run(new ProcessIO(in, out, err)).exitValue()
      reserr + res
    }*/
}