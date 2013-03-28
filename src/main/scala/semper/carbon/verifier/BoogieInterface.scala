package semper.carbon.verifier

import semper.sil.verifier.{Failure, VerificationError, Success, VerificationResult}
import sys.process._
import java.io._
import semper.carbon.boogie._

/**
 * Defines a clean interface to invoke Boogie and get a list of errors back.
 *
 * @author Stefan Heule
 */
trait BoogieInterface {

  def defaultOptions = Seq("/nologo", "/errorTrace:0", s"/z3exe:$z3Path")

  /** The (resolved) path where Boogie is supposed to be located. */
  def boogiePath: String

  /** The (resolved) path where Z3 is supposed to be located. */
  def z3Path: String

  def invokeBoogie(program: Program, options: Seq[String]): VerificationResult = {
    // find all errors and assign everyone a unique id
    var errormap: Map[Int, VerificationError] = Map()
    program.visit {
      case a@Assert(exp, error) =>
        errormap += (a.id -> error)
      case _ =>
    }

    // invoke Boogie
    val output = run(program.toString, defaultOptions ++ options)

    // parse the output
    parse(output) match {
      case Nil =>
        Success
      case errorIds =>
        val errors = errorIds map (errormap.get(_).get)
        Failure(errors)
    }
  }

  /**
   * Parse the output of Boogie.
   */
  private def parse(output: String): Seq[Int] = {
    val SummaryPattern = "Boogie program verifier finished with ([0-9]+) verified, ([0-9]+) errors?".r
    val ErrorPattern = "  .+ \\[([0-9]+)\\]".r
    val errors = collection.mutable.ListBuffer[Int]()
    for (l <- output.split("\r\n")) {
      l match {
        case ErrorPattern(id) =>
          errors += id.toInt
        case SummaryPattern(v, e) =>
          assert(e.toInt == errors.size, s"Found ${errors.size} errors, but there should be $e.")
        case "" => // ignore empty lines
        case _ =>
          sys.error(s"Found an unparsable output from Boogie: $l")
      }
    }
    errors.toSeq
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
    val stream = new BufferedOutputStream(new FileOutputStream(tmp))
    stream.write(input.getBytes)
    stream.close()

    // Note: call exitValue to block until Boogie has finished
    // Note: we call boogie with an empty input "file" on stdin and parse the output
    (Seq(boogiePath) ++ options ++ Seq(tmp.getAbsolutePath)).run(new ProcessIO(_.close(), out, err)).exitValue()
    reserr + res
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
