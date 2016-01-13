/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.impls

import viper.carbon.modules.{StatelessComponent, StmtModule}
import viper.carbon.modules.components.SimpleStmtComponent
import viper.silver.ast.utility.Expressions.{whenExhaling, whenInhaling}
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.verifier.Verifier
import Implicits._
import viper.silver.verifier.errors
import viper.silver.verifier.PartialVerificationError
import viper.silver.ast.utility.Expressions

/**
 * The default implementation of a [[viper.carbon.modules.StmtModule]].
 */
class DefaultStmtModule(val verifier: Verifier) extends StmtModule with SimpleStmtComponent with StatelessComponent {

  import verifier._
  import expModule._
  import stateModule._
  import exhaleModule._
  import inhaleModule._
  import typeModule._
  import funcPredModule._
  import wandModule._

  override def start() {
    // this is the main translation, so it should come at the beginning
    register(this, before = verifier.allModules)
  }

  val lblNamespace = verifier.freshNamespace("stmt.lbl")

  def name = "Statement module"

  /**
   * Takes a list of assertions, and executes all of the unfolding expressions inside. In particular, this means that the correct
   * predicate definitions get assumed, under the correct conditionals. Most checking of definedness is disabled (by the "false"
   * parameter to checkDefinedness), however, note that checking that the predicates themselves are held when unfolding is still
   * performed, because the code for that is an exhale. Because of this, it may be necessary to make sure that this operation is
   * called before/after the corresponding exhale/inhale of the assertions.
   */
  def executeUnfoldings(exps: Seq[sil.Exp], exp_error: (sil.Exp => PartialVerificationError)): Stmt = {
    (exps map (exp => (if (exp.existsDefined[Unit]({case sil.Unfolding(_,_) => })) checkDefinedness(exp, exp_error(exp), false) else Nil:Stmt)))
  }

  override def handleStmt(s: sil.Stmt) : (Stmt,Stmt) =
    s match {
      case s : sil.Fold => translateFold(s)
      case _ => (simpleHandleStmt(s),Statements.EmptyStmt) // put code *first*
    }

  override def simpleHandleStmt(stmt: sil.Stmt): Stmt = {
    stmt match {
      case assign@sil.LocalVarAssign(lhs, rhs) =>
        checkDefinedness(lhs, errors.AssignmentFailed(assign)) ++
          checkDefinedness(rhs, errors.AssignmentFailed(assign)) ++
          Assign(translateExp(lhs), translateExp(rhs))
      case assign@sil.FieldAssign(lhs, rhs) =>
        checkDefinedness(lhs, errors.AssignmentFailed(assign)) ++ 
          checkDefinedness(rhs, errors.AssignmentFailed(assign))
      case fold@sil.Fold(e) => sys.error("Internal error: translation of fold statement cannot be handled by simpleHandleStmt code; found:" + fold.toString())
      case unfold@sil.Unfold(e) =>
        translateUnfold(unfold)
      case inh@sil.Inhale(e) =>
        checkDefinednessOfSpecAndInhale(whenInhaling(e), errors.InhaleFailed(inh))
      case exh@sil.Exhale(e) =>
        val transformedExp = whenExhaling(e)
        checkDefinedness(transformedExp, errors.ExhaleFailed(exh)) ++
          exhale((transformedExp, errors.ExhaleFailed(exh)))
      case a@sil.Assert(e) =>
        val transformedExp = whenExhaling(e)
        if (transformedExp.isPure) {
          // if e is pure, then assert and exhale are the same
          checkDefinedness(transformedExp, errors.AssertFailed(a)) ++
            exhale((transformedExp, errors.AssertFailed(a)))
        } else {
          // we create a temporary state to ignore the side-effects
          val (backup, snapshot) = freshTempState("Assert")
          val exhaleStmt = exhale((transformedExp, errors.AssertFailed(a)))
          replaceState(snapshot)
          checkDefinedness(transformedExp, errors.AssertFailed(a)) :: backup :: exhaleStmt :: Nil
        }
      case mc@sil.MethodCall(methodName, args, targets) =>
        val method = verifier.program.findMethod(methodName)
        // save pre-call state
        val (preCallStateStmt, state) = stateModule.freshTempState("PreCall")
        val preCallState = stateModule.state
        val oldState = stateModule.oldState
        stateModule.replaceState(state)
        val toUndefine = collection.mutable.ListBuffer[sil.LocalVar]()
        val actualArgs = (args.zipWithIndex) map (a => {
          val (actual, i) = a
          // use the concrete argument if it is just a variable or constant (to avoid code bloat)
          val useConcrete = actual match {
            case v: sil.LocalVar if !targets.contains(v) => true
            case _: sil.Literal => true
            case _ => false
          }
          if (!useConcrete) {
            val silFormal = method.formalArgs(i)
            val formal = sil.LocalVar("arg_" + silFormal.name)(silFormal.typ)
            mainModule.env.define(formal)
            toUndefine.append(formal)
            val stmt = translateExp(formal) := translateExp(actual)
            (formal, stmt)
          } else {
            (args(i), Nil: Stmt)
          }
        })
        val pres = method.pres map (e => Expressions.instantiateVariables(e, method.formalArgs ++ method.formalReturns, (actualArgs map (_._1)) ++ targets))
        val posts = method.posts map (e => Expressions.instantiateVariables(e, method.formalArgs ++ method.formalReturns, (actualArgs map (_._1)) ++ targets))
        val res = preCallStateStmt ++
          (targets map (e => checkDefinedness(e, errors.CallFailed(mc)))) ++
          (args map (e => checkDefinedness(e, errors.CallFailed(mc)))) ++
          (actualArgs map (_._2)) ++
          Havoc((targets map translateExp).asInstanceOf[Seq[Var]]) ++
          MaybeCommentBlock("Exhaling precondition", executeUnfoldings(pres, (pre => errors.Internal(pre))) ++ exhale(pres map (e => (e, errors.PreconditionInCallFalse(mc))))) ++ {
          stateModule.replaceOldState(preCallState)
          val res = MaybeCommentBlock("Inhaling postcondition", inhale(posts) ++ executeUnfoldings(posts, (post => errors.Internal(post))))
          stateModule.replaceOldState(oldState)
          toUndefine map mainModule.env.undefine
          res
        }
        res
      case w@sil.While(cond, invs, locals, body) =>
        val guard = translateExp(cond)
        locals map (v => mainModule.env.define(v.localVar)) // add local variables to environment - this should be revisited when scopes are properly implemented
        MaybeCommentBlock("Exhale loop invariant before loop",
          executeUnfoldings(w.invs, (inv => errors.LoopInvariantNotEstablished(inv))) ++ exhale(w.invs map (e => (e, errors.LoopInvariantNotEstablished(e))))
        ) ++
          MaybeCommentBlock("Havoc loop written variables (except locals)", // this should perhaps be revisited when scopes are properly implemented
            Havoc(((w.writtenVars diff (locals map (_.localVar))) map translateExp).asInstanceOf[Seq[Var]]) ++
              (w.writtenVars map (v => mainModule.allAssumptionsAboutValue(v.typ,mainModule.translateLocalVarSig(v.typ, v),false)))
          ) ++
          MaybeCommentBlock("Check definedness of invariant", NondetIf(
            (invs map (inv => checkDefinednessOfSpecAndInhale(inv, errors.WhileFailed(w)))) ++
              Assume(FalseLit())
          )) ++
          MaybeCommentBlock("Check the loop body", NondetIf({
            val (freshStateStmt, prevState) = stateModule.freshTempState("loop")
            val stmts = MaybeComment("Reset state", freshStateStmt ++ stateModule.initBoogieState) ++
              MaybeComment("Inhale invariant", inhale(w.invs) ++ executeUnfoldings(w.invs, (inv => errors.Internal(inv)))) ++
              Comment("Check and assume guard") ++
              checkDefinedness(cond, errors.WhileFailed(w)) ++
              Assume(guard) ++ stateModule.assumeGoodState ++
              MaybeComment("Havoc locals", Havoc((locals map (x => translateExp(x.localVar))).asInstanceOf[Seq[Var]])) ++
              MaybeCommentBlock("Translate loop body", translateStmt(body)) ++
              MaybeComment("Exhale invariant", executeUnfoldings(w.invs, (inv => errors.LoopInvariantNotPreserved(inv))) ++ exhale(w.invs map (e => (e, errors.LoopInvariantNotPreserved(e))))) ++
              MaybeComment("Terminate execution", Assume(FalseLit()))
            stateModule.replaceState(prevState)
            locals map (v => mainModule.env.undefine(v.localVar)) // remove local variables from environment - this should be revisited when scopes are properly implemented
            stmts
          }
          )) ++
          MaybeCommentBlock("Inhale loop invariant after loop, and assume guard",
            Assume(guard.not) ++ stateModule.assumeGoodState ++
              inhale(w.invs) ++ executeUnfoldings(w.invs, (inv => errors.Internal(inv)))
          )
      case fr@sil.Fresh(vars) =>
        MaybeCommentBlock(s"Translation of statement ${fr})", components map (_.freshReads(vars)))
      case fb@sil.Constraining(vars, body) =>
        MaybeCommentBlock(s"Start of constraining(${vars.mkString(", ")})", components map (_.enterConstrainingBlock(fb))) ++
          translateStmt(body) ++
          MaybeCommentBlock(s"End of constraining(${vars.mkString(", ")})", components map (_.leaveConstrainingBlock(fb)))
      case i@sil.If(cond, thn, els) =>
        checkDefinedness(cond, errors.IfFailed(cond)) ++
          If(translateExp(cond),
            translateStmt(thn),
            translateStmt(els))
      case sil.Label(name) => {
        val (stmt, currentState) = stateModule.freshTempState("Label" + name)
        stateModule.stateRepositoryPut(name, stateModule.state)
        stateModule.replaceState(currentState)
        stmt ++ Label(Lbl(Identifier(name)(lblNamespace)))
      }
      case sil.Goto(target) =>
        Goto(Lbl(Identifier(target)(lblNamespace)))
      case sil.NewStmt(target,fields) =>
        Nil
      case pa@sil.Package(wand) =>
      // checkDefinedness(wand, errors.MagicWandNotWellformed(wand))
        translatePackage(pa,errors.PackageFailed(pa))
      case a@sil.Apply(wand) =>
        translateApply(a, errors.ApplyFailed(a))
      case _: sil.Seqn =>
        Nil
    }
  }

  override def translateStmt(stmt: sil.Stmt): Stmt = {
    var comment = "Translating statement: " + stmt.toString.replace("\n", "\n  // ")
    stmt match {
      case sil.Seqn(ss) =>
        // return to avoid adding a comment, and to avoid the extra 'assumeGoodState'
        return Seqn(ss map translateStmt)
      case sil.If(cond, thn, els) =>
        comment = s"Translating statement: if ($cond)"
      case sil.While(cond, invs, local, body) =>
        comment = s"Translating statement: while ($cond)"
      case fr@sil.Fresh(vars)  =>
        comment = s"Translating statement: fresh ${vars.mkString(", ")} "
      case cs@sil.Constraining(vars,body) =>
        comment = s"Translating statement: constraining(${vars.mkString(", ")})"
      case _ =>
    }

    def isComposite(stmt: sil.Stmt): Boolean = {
      stmt match {
        case _: sil.If => true
        case _: sil.While => true
        case _: sil.Seqn => true
        case _ => false
      }
    }

    var stmts = Seqn(Nil)
    for (c <- components.reverse) { // reverse order, so that "first" component contributes first (outermost) code
      val (before, after) = c.handleStmt(stmt)
      stmts = before ++ stmts ++ after
    }
    if (stmts.children.size == 0) {
      assert(assertion = false, "Translation of " + stmt + " is not defined")
    }
    val translation = stmts ::
      assumeGoodState ::
      Nil

    CommentBlock(comment + s" -- ${stmt.pos}", translation)
  }
}
