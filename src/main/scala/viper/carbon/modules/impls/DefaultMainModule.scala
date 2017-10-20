/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.impls

import viper.carbon.modules._
import viper.silver.ast.utility.Expressions
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
import viper.silver.ast.utility.Rewriter.Traverse

/**
 * The default implementation of a [[viper.carbon.modules.MainModule]].
 */
class DefaultMainModule(val verifier: Verifier) extends MainModule with StatelessComponent {

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
      p.transform(
        { case f: sil.Forall => f.autoTrigger },
        Traverse.TopDown)
    )

    val output = verifier.program match {
      case sil.Program(domains, fields, functions, predicates, methods) =>
        // translate all members
        val translateFields =
          MaybeCommentedDecl("Translation of all fields", (fields flatMap translateField).toList)
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
          s"Translation of Viper program.",
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
          case method @ sil.Method(name, formalArgs, formalReturns, pres, posts, _) =>
            val initOldStateComment = "Initializing of old state"
            val ins: Seq[LocalVarDecl] = formalArgs map translateLocalVarDecl
            val outs: Seq[LocalVarDecl] = formalReturns map translateLocalVarDecl
            val init = MaybeCommentBlock("Initializing the state", stateModule.initBoogieState ++ assumeAllFunctionDefinitions)
            val initOld = MaybeCommentBlock("Initializing the old state", stateModule.initOldState)
            val paramAssumptions = m.formalArgs map (a => allAssumptionsAboutValue(a.typ, translateLocalVarDecl(a), true))
            val inhalePre = translateMethodDeclPre(pres)
            val checkPost: Stmt = if (posts.nonEmpty) {
              translateMethodDeclCheckPosts(posts)
            }
            else Nil
            val postsWithErrors = posts map (p => (p, errors.PostconditionViolated(p, m)))
            val exhalePost = MaybeCommentBlock("Exhaling postcondition", exhale(postsWithErrors))
            val body: Stmt = translateStmt(method.bodyOrAssumeFalse)
              /* TODO: Might be worth special-casing on methods with empty bodies */
            val proc = Procedure(Identifier(name), ins, outs,
              Seq(init,
                MaybeCommentBlock("Assumptions about method arguments", paramAssumptions),
                inhalePre,
            MaybeCommentBlock(initOldStateComment, initOld), checkPost,
            body, exhalePost))
        CommentedDecl(s"Translation of method $name", proc)
    }
    env = null
    res
  }

  private def translateMethodDeclCheckPosts(posts: Seq[sil.Exp]): Stmt = {
    val (stmt, state) = stateModule.freshTempState("Post")

    val reset = stateModule.resetBoogieState

    // note that the order here matters - onlyExhalePosts should be computed with respect to the reset state
    val onlyExhalePosts: Seq[Stmt] = checkDefinednessOfExhaleSpecAndInhale(
    posts, {
      errors.ContractNotWellformed(_)
    })

    val stmts = stmt ++ reset ++ (
    if (Expressions.contains[sil.InhaleExhaleExp](posts)) {
      // Postcondition contains InhaleExhale expression.
      // Need to check inhale and exhale parts separately.
      val onlyInhalePosts: Seq[Stmt] = checkDefinednessOfInhaleSpecAndInhale(
      posts, {
        errors.ContractNotWellformed(_)
      })

          NondetIf(
          MaybeComment("Checked inhaling of postcondition to check definedness",
            MaybeCommentBlock("Do welldefinedness check of the inhale part.",
              NondetIf(onlyInhalePosts ++ Assume(FalseLit()))) ++
              MaybeCommentBlock("Normally inhale the exhale part.",
                onlyExhalePosts)
          ) ++
            MaybeComment("Stop execution", Assume(FalseLit()))
      )
    }
    else {
      NondetIf(
        MaybeComment("Checked inhaling of postcondition to check definedness", onlyExhalePosts) ++
          MaybeComment("Stop execution", Assume(FalseLit()))
      )
    })

    stateModule.replaceState(state)

    stmts
  }

  private def translateMethodDeclPre(pres: Seq[sil.Exp]): Stmt = {
    stateModule.setTreatOldAsCurrentState(true)
    val res = if (Expressions.contains[sil.InhaleExhaleExp](pres)) {
      // Precondition contains InhaleExhale expression.
      // Need to check inhale and exhale parts separately.
      val onlyExhalePres: Seq[Stmt] = checkDefinednessOfExhaleSpecAndInhale(
      pres, {
        errors.ContractNotWellformed(_)
      })
      val onlyInhalePres: Seq[Stmt] = checkDefinednessOfInhaleSpecAndInhale(
      pres, {
        errors.ContractNotWellformed(_)
      })
      MaybeCommentBlock("Checked inhaling of precondition",
        MaybeCommentBlock("Do welldefinedness check of the exhale part.",
          NondetIf(onlyExhalePres ++ Assume(FalseLit()))) ++
          MaybeCommentBlock("Normally inhale the inhale part.",
            onlyInhalePres)
      )
    }
    else {
      val inhalePres: Seq[Stmt] = checkDefinednessOfInhaleSpecAndInhale(
      pres, {
        errors.ContractNotWellformed(_)
      })
      MaybeCommentBlock("Checked inhaling of precondition", inhalePres)
    }

    stateModule.setTreatOldAsCurrentState(false)
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
