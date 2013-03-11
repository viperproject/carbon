package semper.carbon.modules.impls

import semper.carbon.modules._
import semper.sil.{ast => sil}
import semper.carbon.boogie.{CommentedDecl, Procedure, Decl, Program}
import semper.carbon.boogie.Implicits._
import java.text.SimpleDateFormat
import java.util.Date

/**
 * The default implementation of a [[semper.carbon.modules.MainModule]].
 *
 * @author Stefan Heule
 */
class DefaultMainModule(val verifier: Verifier) extends MainModule with AllModule {
  def name = "Main module"

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
          "Date:      " + new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(new Date()),
          "Tool:      " + verifier.toolDesc,
          "Arguments: " + verifier.fullCmd,
          "Dependencies:"
        ) ++ deps ++
          Seq("")
        Program(header, preambles ++ members)
    }
  }

  def translateMethod(m: sil.Method): Seq[Decl] = {
    m match {
      case sil.Method(name, formalArgs, formalReturns, pres, posts, locals, body) =>
        // TODO: handle pre/post
        // TODO: handle arguments
        // TODO: handle locals
        val tBody = translateStmt(body)
        val proc = Procedure(name, Nil, Nil, tBody)
        CommentedDecl(s"Translation of method $name", proc)
    }
  }

  def translateFunction(f: sil.Function): Seq[Decl] = ???
  def translateDomain(d: sil.Domain): Seq[Decl] = ???
  def translateFieldDecl(f: sil.Field): Seq[Decl] = ???
  def translatePredicate(p: sil.Predicate): Seq[Decl] = ???
}
