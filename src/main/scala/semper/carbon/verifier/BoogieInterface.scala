package semper.carbon.verifier

import semper.sil.verifier._
import sys.process._
import java.io._
import semper.carbon.boogie._
import semper.sil.verifier.Failure
import semper.carbon.boogie.Assert
import semper.carbon.boogie.Program
import semper.sil.ast.{NoPosition, Position}

/**
 * Defines a clean interface to invoke Boogie and get a list of errors back.
 */
trait BoogieInterface {

  def defaultOptions = Seq("/nologo", "/vcsCores:" + java.lang.Runtime.getRuntime.availableProcessors, "/errorTrace:0", s"/z3exe:$z3Path")

  /** The (resolved) path where Boogie is supposed to be located. */
  def boogiePath: String

  /** The (resolved) path where Z3 is supposed to be located. */
  def z3Path: String

  var errormap: Map[Int, VerificationError] = Map()
  def invokeBoogie(program: Program, options: Seq[String]): VerificationResult = {
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
    val SummaryPattern = "Boogie program verifier finished with ([0-9]+) verified, ([0-9]+) error.*".r
    val ErrorPattern = "  .+ \\[([0-9]+)\\]".r
    val errors = collection.mutable.ListBuffer[Int]()
    var otherErrId = 0

    val unexpected : (String => Unit) = ((msg:String) => {
      otherErrId -= 1

      errors += otherErrId
      val internalError = new AbstractVerificationError {
        protected def text: String = msg

        def id: String = "boogie.unknown.output"

        def reason: ErrorReason = new ErrorReason {
          def pos: Position = NoPosition

          def readableMessage: String = "?"

          def id: String = "unknown"

          def offendingNode = null
        }

        def offendingNode = null

        override def pos = NoPosition

        override def readableMessage(withId: Boolean, withPosition: Boolean) =
          s"Internal error: $text"
      }
      errormap += (otherErrId -> internalError)
    })

    for (l <- output.linesIterator) {
      l match {
        case ErrorPattern(id) =>
          errors += id.toInt
        case SummaryPattern(v, e) =>
          if(e.toInt != errors.size) unexpected(s"Found ${errors.size} errors, but there should be $e. The output was: $output")
        case "" => // ignore empty lines
        case _ =>
          unexpected(s"Found an unparsable output from Boogie: $l")
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
    //tmp.deleteOnExit()
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
