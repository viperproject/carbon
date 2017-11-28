/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.verifier

import viper.silver.verifier._

import sys.process._
import java.io._

import viper.carbon.boogie._
import viper.silver.verifier.Failure
import viper.silver.verifier.errors.{ErrorNode, Internal}
import viper.silver.verifier.reasons.InternalReason
import viper.carbon.boogie.Assert
import viper.carbon.boogie.Program
import viper.silver.ast.{NoPosition, Position, Positioned}

class BoogieDependency(_location: String) extends Dependency {
  def name = "Boogie"
  def location = _location
  var version = "" // filled-in when Boogie is invoked
}

/**
 * Defines a clean interface to invoke Boogie and get a list of errors back.
 */

trait BoogieInterface {

  def defaultOptions = Seq("/vcsCores:" + java.lang.Runtime.getRuntime.availableProcessors, "/errorTrace:0", "/errorLimit:10000000", "/noinfer", "/z3opt:smt.qi.max_multi_patterns=1000", s"/z3exe:$z3Path")

  /** The (resolved) path where Boogie is supposed to be located. */
  def boogiePath: String

  /** The (resolved) path where Z3 is supposed to be located. */
  def z3Path: String

  private var _boogieProcess:Process = null

  var errormap: Map[Int, VerificationError] = Map()
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
      case (version,errorIds) =>
        val errors = errorIds map (errormap.get(_).get)
        (version,Failure(errors))
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

    for (l <- output.linesIterator) {
      l match {
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
    def out(input: java.io.InputStream) {
      res += convertStreamToString(input)
      input.close()
    }
    def err(in: java.io.InputStream) {
      reserr += convertStreamToString(in)
      in.close()
    }
    // write program to a temporary file
    val tmp = File.createTempFile("carbon", ".bpl")
    tmp.deleteOnExit()
    val stream = new BufferedOutputStream(new FileOutputStream(tmp))
    stream.write(input.getBytes)
    stream.close()

    // Note: call exitValue to block until Boogie has finished
    // Note: we call boogie with an empty input "file" on stdin and parse the output
    _boogieProcess = (Seq(boogiePath) ++ options ++ Seq(tmp.getAbsolutePath)).run(new ProcessIO(_.close(), out, err))
    _boogieProcess.exitValue()
    reserr + res
  }

  def stopBoogie(){
    if(_boogieProcess!= null){
      _boogieProcess.destroy()
      _boogieProcess.exitValue() //TODO: this blocks if an underlying z3 instance remains running
    }
  }

  // TODO: investigate why passing the program directly does not work
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
  }
}