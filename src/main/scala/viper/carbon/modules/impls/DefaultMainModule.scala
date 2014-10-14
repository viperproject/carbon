/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.impls

import viper.carbon.modules._
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.boogie.Implicits._
import java.text.SimpleDateFormat
import java.util.Date
import viper.carbon.boogie.CommentedDecl
import viper.carbon.boogie.Procedure
import viper.carbon.boogie.Program
import viper.carbon.verifier.Environment
import viper.silver.verifier.errors
import viper.carbon.verifier.Verifier

/**
 * The default implementation of a [[viper.carbon.modules.MainModule]].
 */
class DefaultMainModule(val verifier: Verifier) extends MainModule {

  import verifier._
  import typeModule._
  import stmtModule._
  import exhaleModule._
  import heapModule._
  import funcPredModule._
  import domainModule._
  import expModule._

  def name = "Main module"

  override val silVarNamespace = verifier.freshNamespace("main.silver")
  implicit val mainNamespace = verifier.freshNamespace("main")

  override def translateLocalVarSig(typ:sil.Type, v:sil.LocalVar): LocalVarDecl = {
    val t: Type = translateType(typ)
    val name: Identifier = env.get(v).name
    LocalVarDecl(name, t)
  }

  override def translate(p: sil.Program): Program = {

    verifier.replaceProgram(
      p.transform({
        case f: sil.Forall =>
           f.autoTrigger

      })((_) => true)
    )

    val output = verifier.program match {
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
          s"Translation of SIL program.",
          "",
          "Date:         " + new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(new Date()),
          "Tool:         " + verifier.toolDesc) ++
          (verifier.getDebugInfo map (a => a._1 + ": " + (" " * (12 - a._1.size)) + a._2)) ++
          Seq("Dependencies:") ++
          deps ++
          Seq("")
        Program(header, preambles ++ members)
    }

    output.optimize.asInstanceOf[Program]
  }

  def translateMethodDecl(m: sil.Method): Seq[Decl] = {
    env = Environment(verifier, m)
    val res = m match {
      case sil.Method(name, formalArgs, formalReturns, pres, posts, locals, b) =>
        val initOldStateComment = "Initializing of old state"
        val ins: Seq[LocalVarDecl] = formalArgs map translateLocalVarDecl
        val outs: Seq[LocalVarDecl] = formalReturns map translateLocalVarDecl
        val init = MaybeCommentBlock("Initializing the state", stateModule.initState ++ assumeAllFunctionDefinitions)
        val initOld = stateModule.initOldState
        val paramAssumptions = m.formalArgs map (a => allAssumptionsAboutValue(a.typ, translateLocalVarDecl(a), true))
        val localAssumptions = m.locals map (a => allAssumptionsAboutValue(a.typ, translateLocalVarDecl(a), true))
        val inhalePre = MaybeCommentBlock("Checked inhaling of precondition",
          pres map (e => checkDefinednessOfSpecAndInhale(e, errors.ContractNotWellformed(e))))
        val checkPost: Stmt = if (posts.nonEmpty) NondetIf(
          MaybeComment("Checked inhaling of postcondition to check definedness",
            posts map (e => checkDefinednessOfSpecAndInhale(e, errors.ContractNotWellformed(e)))) ++
            MaybeComment("Stop execution", Assume(FalseLit())), Nil)
        else Nil
        val postsWithErrors = posts map (p => (p, errors.PostconditionViolated(p, m)))
        val exhalePost = MaybeCommentBlock("Exhaling postcondition", exhale(postsWithErrors))
        val body: Stmt = translateStmt(b)
        val proc = Procedure(Identifier(name), ins, outs,
          Seq(init,
            MaybeCommentBlock("Assumptions about method arguments", paramAssumptions),
            MaybeCommentBlock("Assumptions about local variables", localAssumptions),
            inhalePre,
            MaybeCommentBlock(initOldStateComment, initOld), checkPost,
            body, exhalePost))
        CommentedDecl(s"Translation of method $name", proc)
    }
    env = null
    res
  }

  override def allAssumptionsAboutValue(typ:sil.Type, arg: LocalVarDecl, isParameter:Boolean): Stmt = {
    val tmp = verifier.allModules map (_.validValue(typ, arg.l, isParameter))
    val assumptions = tmp.filter(_.isDefined).map(_.get)
    assumptions.allOption match {
      case None => Nil
      case Some(e) => Assume(e)
    }
  }

  def translateDomainDecl(d: sil.Domain): Seq[Decl] = {
    env = Environment(verifier, d)
    val res = translateDomain(d)
    env = null
    res
  }
}
