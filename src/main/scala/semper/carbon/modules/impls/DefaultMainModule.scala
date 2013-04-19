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
import semper.sil.verifier.errors

/**
 * The default implementation of a [[semper.carbon.modules.MainModule]].
 *
 * @author Stefan Heule
 */
class DefaultMainModule(val verifier: Verifier) extends MainModule {

  import verifier._
  import typeModule._
  import stmtModule._
  import stateModule._
  import exhaleModule._
  import heapModule._
  import inhaleModule._
  import funcPredModule._
  import domainModule._
  import expModule._

  def name = "Main module"

  override val silVarNamespace = verifier.freshNamespace("main.silvar")
  implicit val mainNamespace = verifier.freshNamespace("main")

  override def translateLocalVarDecl(l: sil.LocalVarDecl): LocalVarDecl = {
    val typ: Type = translateType(l.typ)
    val name: Identifier = env.get(l.localVar).name
    // ask all modules to contribute to the where clause if they want to
    val wheres = verifier.allModules map (_.whereClause(l.typ, LocalVar(name, typ)))
    val where = wheres.filter(_.isDefined).map(_.get)
    LocalVarDecl(name, typ, where.allOption)
  }

  override def translate(p: sil.Program): Program = {
    p match {
      case sil.Program(domains, fields, functions, predicates, methods) =>
        // translate all members
        val translateFields =
          MaybeCommentedDecl("Translation of all fields", fields flatMap translateField)
        val members = (domains flatMap translateDomainDecl) ++
          translateFields ++
          (functions flatMap translateFunction) ++
          (predicates flatMap translatePredicate) ++
          (methods flatMap translateMethodDecl)

        // get the preambles (only at the end, even if we add it at the beginning)
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
          (verifier.getDebugInfo map (a => a._1 + ": " + (" " * (12 - a._1.size)) + a._2)) ++
          Seq("Dependencies:") ++
          deps ++
          Seq("")
        Program(header, preambles ++ members)
    }
  }

  def translateMethodDecl(m: sil.Method): Seq[Decl] = {
    env = Environment(verifier, m)
    val res = m match {
      case sil.Method(name, formalArgs, formalReturns, pres, posts, locals, b) =>
        val ins: Seq[LocalVarDecl] = formalArgs map translateLocalVarDecl
        val outs: Seq[LocalVarDecl] = formalReturns map translateLocalVarDecl
        val init = MaybeCommentBlock("Initializing the state", initState)
        val initOld = initOldState
        val checkPrePost = MaybeCommentBlock("Check definedness of pre/postcondition", NondetIf(
          (pres map (e => checkDefinednessOfSpec(e, errors.ContractNotWellformed(e)))) ++
            initOld ++
            (posts map (e => checkDefinednessOfSpec(e, errors.ContractNotWellformed(e))))
            ++ Assume(FalseLit())
        ))
        val inhalePre = MaybeCommentBlock("Inhaling precondition", inhale(pres))
        val body: Stmt = translateStmt(b)
        val postsWithErrors = posts map (p => (p, errors.PostconditionViolated(p, m)))
        val exhalePost = MaybeCommentBlock("Exhaling postcondition", exhale(postsWithErrors))
        val proc = Procedure(Identifier(name), ins, outs, Seq(init, checkPrePost, initOld, inhalePre, body, exhalePost))
        CommentedDecl(s"Translation of method $name", proc)
    }
    env = null
    res
  }

  def translateDomainDecl(d: sil.Domain): Seq[Decl] = {
    env = Environment(verifier, d)
    val res = translateDomain(d)
    env = null
    res
  }
}
