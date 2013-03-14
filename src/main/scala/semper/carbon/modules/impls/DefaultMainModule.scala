package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.boogie.Implicits._
import java.text.SimpleDateFormat
import java.util.Date
import semper.carbon.verifier.Verifier
import semper.carbon.boogie.CommentedDecl
import semper.carbon.boogie.Procedure
import semper.carbon.boogie.Program
import semper.carbon.verifier.Environment

/**
 * The default implementation of a [[semper.carbon.modules.MainModule]].
 *
 * @author Stefan Heule
 */
class DefaultMainModule(val verifier: Verifier) extends MainModule {

  import verifier.typeModule._
  import verifier.stmtModule._
  import verifier.stateModule._

  def name = "Main module"

  /** The current environment. */
  var _env: Environment = null
  override def env = _env

  override def translateLocalVarDecl(l: sil.LocalVarDecl): LocalVarDecl = {
    LocalVarDecl(env.get(l.localVar).name, translateType(l.typ))
  }

  override def translate(p: sil.Program): Program = {
    p match {
      case sil.Program(name, domains, fields, functions, predicates, methods) =>
        // translate all members
        val members = (domains flatMap translateDomain) ++
          (fields flatMap translateFieldDecl) ++
          (functions flatMap translateFunction) ++
          (predicates flatMap translatePredicate) ++
          (methods flatMap translateMethod)

        // get the preambles
        val preambles = verifier.allModules flatMap {
          m =>
            if (m.preamble.size > 0) Seq(CommentedDecl(s"Preamble of ${m.name}.", m.preamble))
            else Nil
        }

        // some header information for debugging
        val deps = verifier.dependencyDescs map ("  " + _)
        val header = Seq(
          "",
          s"Translation of SIL program '$name'.",
          "",
          "Date:         " + new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(new Date()),
          "Tool:         " + verifier.toolDesc) ++
          (verifier.debugInfo map (a => a._1 + ": " + (" " * (12 - a._1.size)) + a._2)) ++
          Seq("Dependencies:") ++
          deps ++
          Seq("")
        Program(header, preambles ++ members)
    }
  }

  def translateMethod(m: sil.Method): Seq[Decl] = {
    _env = Environment(verifier, m)
    val res = m match {
      case sil.Method(name, formalArgs, formalReturns, pres, posts, locals, b) =>
        // TODO: handle pre/post
        val ins: Seq[LocalVarDecl] = formalArgs map translateLocalVarDecl
        val outs: Seq[LocalVarDecl] = formalReturns map translateLocalVarDecl
        val init = initState
        val body: Stmt = translateStmt(b)
        val proc = Procedure(name, ins, outs, Seqn(Seq(init, body)))
        CommentedDecl(s"Translation of method $name", proc)
    }
    _env = null
    res
  }

  def translateFunction(f: sil.Function): Seq[Decl] = ???
  def translateDomain(d: sil.Domain): Seq[Decl] = ???
  def translateFieldDecl(f: sil.Field): Seq[Decl] = ???
  def translatePredicate(p: sil.Predicate): Seq[Decl] = ???
}
