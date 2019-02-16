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
  import funcPredModule._
  import wandModule._

  override def start() {
    // this is the main translation, so it should come at the "beginning"; it defines the innermost code used in the translation; other modules can wrap this with their own code
    register(this, before = Seq(verifier.heapModule,verifier.permModule))
    // NOTE: this builds up the translation inside-out, so the *first* component defines the innermost code.
    // This works as follows, for statement translation: StmtModule, then PermModule, then HeapModule
    // For Fold statements: Heap module adds version/secondary mask code as a postfix to the main code from the StmtModule
    // For Field assignments: Heap module (which goes last) adds the translation of the actual operation as a postfix the other code (which checks well-definedness)
    // For MethodCall: assumptions about return values are added by the HeapModule as a postfix to the main translation in StmtModule
    // For New: the operation translation (HeapModule) is added as a prefix to the code adding permissions (PermModule)
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

  /**
    * @param statesStackForPackageStmt stack of states used in translating package statements
    * @param insidePackageStmt Boolean that represents whether 'stmt' is being translated inside package statement or not
    * @param allStateAssms represents all assumptions about states on the statesStack
    *
    * These wand-related parameters are used when the method is called during packaging a wand.
    * For more details see the general node in 'wandModule'
    */
  override def handleStmt(s: sil.Stmt, statesStackForPackageStmt: List[Any] = null, allStateAssms: Exp = TrueLit(), insidePackageStmt: Boolean = false) : (Seqn => Seqn) = {
    val (bef, aft) =
      s match {
        case s: sil.Fold => translateFold(s, statesStackForPackageStmt, insidePackageStmt)
        case _ => (simpleHandleStmt(s, statesStackForPackageStmt, allStateAssms, insidePackageStmt), Statements.EmptyStmt) // put code *first*
      }
    stmts => bef ++ stmts ++ aft
  }

  /**
    * @param statesStack stack of states used in translating statements during packaging a wand (carries currentState and LHS of wands)
    * @param insidePackageStmt Boolean that represents whether 'stmt' is being translated inside package statement or not
    * @param allStateAssms represents all assumptions about states on the statesStack
    *
    * These wand-related parameters are used when the method is called during packaging a wand.
    * For more details see the general node in 'wandModule'
    */
  override def simpleHandleStmt(stmt: sil.Stmt, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), insidePackageStmt: Boolean = false): Stmt = {
    stmt match {
      case assign@sil.LocalVarAssign(lhs, rhs) =>
        checkDefinedness(lhs, errors.AssignmentFailed(assign), insidePackageStmt = insidePackageStmt) ++
          checkDefinedness(rhs, errors.AssignmentFailed(assign), insidePackageStmt = insidePackageStmt) ++
        {if(insidePackageStmt)
          Assign(translateExpInWand(lhs), translateExpInWand(rhs))
        else
          Assign(translateExp(lhs), translateExp(rhs))}
      case assign@sil.FieldAssign(lhs, rhs) =>
        checkDefinedness(lhs.rcv, errors.AssignmentFailed(assign)) ++
          checkDefinedness(rhs, errors.AssignmentFailed(assign))
      case fold@sil.Fold(e) => sys.error("Internal error: translation of fold statement cannot be handled by simpleHandleStmt code; found:" + fold.toString())
      case unfold@sil.Unfold(e) =>
        translateUnfold(unfold, statesStack, insidePackageStmt)
      case inh@sil.Inhale(e) =>
        checkDefinednessOfSpecAndInhale(whenInhaling(e), errors.InhaleFailed(inh), statesStack, insidePackageStmt)
      case exh@sil.Exhale(e) =>
        val transformedExp = whenExhaling(e)
        checkDefinedness(transformedExp, errors.ExhaleFailed(exh), insidePackageStmt = insidePackageStmt, ignoreIfInWand = true)++
        exhale((transformedExp, errors.ExhaleFailed(exh)), statesStackForPackageStmt = statesStack, insidePackageStmt = insidePackageStmt)
      case a@sil.Assert(e) =>
        val transformedExp = whenExhaling(e)
        if (transformedExp.isPure) {
          // if e is pure, then assert and exhale are the same
          checkDefinedness(transformedExp, errors.AssertFailed(a), insidePackageStmt = insidePackageStmt, ignoreIfInWand = true) ++
            exhale((transformedExp, errors.AssertFailed(a)), statesStackForPackageStmt = statesStack, insidePackageStmt = insidePackageStmt)
        } else {
          // we create a temporary state to ignore the side-effects
          val (backup, snapshot) = freshTempState("Assert")
          val exhaleStmt = exhale((transformedExp, errors.AssertFailed(a)), isAssert =  true, statesStackForPackageStmt = statesStack, insidePackageStmt = insidePackageStmt, havocHeap = false)
          replaceState(snapshot)
            checkDefinedness(transformedExp, errors.AssertFailed(a), insidePackageStmt = insidePackageStmt, ignoreIfInWand = true) :: backup :: exhaleStmt :: Nil
        }
      case mc@sil.MethodCall(methodName, args, targets) =>
        val method = verifier.program.findMethod(methodName)
        // save pre-call state
        val (preCallStateStmt, state) = stateModule.freshTempState("PreCall")
        val preCallState = stateModule.state
        val oldState = stateModule.oldState
        stateModule.replaceState(state)
        val toUndefine = collection.mutable.ListBuffer[sil.LocalVar]()
        val actualArgs = args.zipWithIndex map (a => {
          val (actual, i) = a
          // use the concrete argument if it is just a variable or constant (to avoid code bloat)
          val useConcrete = actual match {
            case v: sil.LocalVar if !targets.contains(v) => true
            case _: sil.Literal => true
            case _ => false
          }
          if (!useConcrete) {
            val silFormal = method.formalArgs(i)
            val tempArg = sil.LocalVar("arg_" + silFormal.name)(silFormal.typ)
            mainModule.env.define(tempArg)
            toUndefine.append(tempArg)
            val translatedTempArg = translateExp(tempArg)
            val translatedActual = translateExp(actual)
            val stmt = translatedTempArg := translatedActual
            (tempArg, stmt, Some(actual))
          } else {
            (args(i), Nil: Stmt, None)
          }
        })
        val neededRenamings : Seq[(sil.AbstractLocalVar, sil.Exp)] = actualArgs.filter((_._3.isDefined)).map(element => (element._1.asInstanceOf[sil.LocalVar],element._3.get))
        val removingTriggers: (errors.ErrorNode => errors.ErrorNode) =
          ((n: errors.ErrorNode) => n.transform{case q: sil.Forall => q.copy(triggers = Nil)(q.pos, q.info, q.errT)})
        val renamingArguments : (errors.ErrorNode => errors.ErrorNode) = ((n:errors.ErrorNode) => removingTriggers(n).transform({
          case e:sil.Exp => Expressions.instantiateVariables[sil.Exp](e,neededRenamings map (_._1), neededRenamings map (_._2))
        }))

        val pres = method.pres map (e => Expressions.instantiateVariables(e, method.formalArgs ++ method.formalReturns, (actualArgs map (_._1)) ++ targets))
        val posts = method.posts map (e => Expressions.instantiateVariables(e, method.formalArgs ++ method.formalReturns, (actualArgs map (_._1)) ++ targets))
        val res = preCallStateStmt ++
          (targets map (e => checkDefinedness(e, errors.CallFailed(mc), insidePackageStmt = insidePackageStmt))) ++
          (args map (e => checkDefinedness(e, errors.CallFailed(mc), insidePackageStmt = insidePackageStmt))) ++
          (actualArgs map (_._2)) ++
          Havoc((targets map translateExp).asInstanceOf[Seq[Var]]) ++
          MaybeCommentBlock("Exhaling precondition", executeUnfoldings(pres, (pre => errors.PreconditionInCallFalse(mc).withReasonNodeTransformed(renamingArguments))) ++
            exhale(pres map (e => (e, errors.PreconditionInCallFalse(mc).withReasonNodeTransformed(renamingArguments))), statesStackForPackageStmt = statesStack, insidePackageStmt = insidePackageStmt)) ++ {
          stateModule.replaceOldState(preCallState)
          val res = MaybeCommentBlock("Inhaling postcondition", inhale(posts, statesStack, insidePackageStmt) ++
            executeUnfoldings(posts, (post => errors.Internal(post).withReasonNodeTransformed(renamingArguments))))
          stateModule.replaceOldState(oldState)
          toUndefine map mainModule.env.undefine
          res
        }
        res
      case w@sil.While(cond, invs, body) =>
        val guard = translateExp(cond)
        MaybeCommentBlock("Exhale loop invariant before loop",
          executeUnfoldings(w.invs, (inv => errors.LoopInvariantNotEstablished(inv))) ++ exhale(w.invs map (e => (e, errors.LoopInvariantNotEstablished(e))))
        ) ++ {
          val writtenVars = w.writtenVars diff (body.transitiveScopedDecls.collect {case l: sil.LocalVarDecl => l} map (_.localVar))
          MaybeCommentBlock("Havoc loop written variables (except locals)",
            Havoc((writtenVars map translateExp).asInstanceOf[Seq[Var]]) ++
              (writtenVars map (v => mainModule.allAssumptionsAboutValue(v.typ,mainModule.translateLocalVarSig(v.typ, v),false)))
          )} ++
          MaybeCommentBlock("Check definedness of invariant", NondetIf(
            (invs map (inv => checkDefinednessOfSpecAndInhale(inv, errors.ContractNotWellformed(inv)))) ++
              Assume(FalseLit())
          )) ++
          MaybeCommentBlock("Check the loop body", NondetIf({
            val (freshStateStmt, prevState) = stateModule.freshTempState("loop")
            val stmts = MaybeComment("Reset state", freshStateStmt ++ stateModule.initBoogieState) ++
              MaybeComment("Inhale invariant", inhale(w.invs) ++ executeUnfoldings(w.invs, (inv => errors.Internal(inv)))) ++
              Comment("Check and assume guard") ++
              checkDefinedness(cond, errors.WhileFailed(w.cond)) ++
              Assume(guard) ++ stateModule.assumeGoodState ++
              MaybeCommentBlock("Translate loop body", translateStmt(body)) ++
              MaybeComment("Exhale invariant", executeUnfoldings(w.invs, (inv => errors.LoopInvariantNotPreserved(inv))) ++ exhale(w.invs map (e => (e, errors.LoopInvariantNotPreserved(e))))) ++
              MaybeComment("Terminate execution", Assume(FalseLit()))
            stateModule.replaceState(prevState)
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
        checkDefinedness(cond, errors.IfFailed(cond), insidePackageStmt = insidePackageStmt) ++
        If((allStateAssms) ==> translateExpInWand(cond),
          translateStmt(thn, statesStack, allStateAssms, insidePackageStmt),
          translateStmt(els, statesStack, allStateAssms, insidePackageStmt))
      case sil.Label(name, invs) => {
        val (stmt, currentState) = stateModule.freshTempState("Label" + name)
        stateModule.stateRepositoryPut(name, stateModule.state)
        stateModule.replaceState(currentState)
        stmt ++ Label(Lbl(Identifier(name)(lblNamespace)))
      }
      case sil.Goto(target) =>
        Goto(Lbl(Identifier(target)(lblNamespace)))
      case pa@sil.Package(wand, proof) => {
        checkDefinedness(wand, errors.MagicWandNotWellformed(wand), insidePackageStmt = insidePackageStmt)
        translatePackage(pa, errors.PackageFailed(pa), statesStack, allStateAssms, insidePackageStmt)
      }
      case a@sil.Apply(wand) =>
        translateApply(a, errors.ApplyFailed(a), statesStack, allStateAssms, insidePackageStmt)
      case _ =>
        Nil
    }
  }

  /**
    * @param statesStack   stack of states used in translating package statements (carries currentState and LHS of wands)
    * @param duringPackage Boolean that represents whether this exhale is inside package statement or not
    * @param allStateAssms represents all assumptions about states on the statesStack
    *
    * These wand-related parameters are used when the method is called during packaging a wand.
    * For more details see the general node in 'wandModule'
    */
  override def translateStmt(stmt: sil.Stmt, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), duringPackage: Boolean = false): Stmt = {
    if(duringPackage) {
        wandModule.translatingStmtsInWandInit()
      }
    var comment = "Translating statement: " + stmt.toString.replace("\n", "\n  // ")
    stmt match {
      case sil.Seqn(ss, scopedDecls) =>
        val locals = scopedDecls.collect {case l: sil.LocalVarDecl => l}
        locals map (v => mainModule.env.define(v.localVar)) // add local variables to environment
        val s =
          MaybeCommentBlock("Assumptions about local variables", locals map (a => mainModule.allAssumptionsAboutValue(a.typ, mainModule.translateLocalVarDecl(a), true))) ++
          Seqn(ss map (st => translateStmt(st, statesStack, allStateAssms, duringPackage)))
        locals map (v => mainModule.env.undefine(v.localVar)) // remove local variables from environment
        // return to avoid adding a comment, and to avoid the extra 'assumeGoodState'
        return s
      case sil.If(cond, thn, els) =>
        comment = s"Translating statement: if ($cond)"
      case sil.While(cond, invs, body) =>
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
    for (c <- components) { // NOTE: this builds up the translation inside-out, so the *first* component defines the innermost code.
      //      val (before, after) = c.handleStmt(stmt, statesStack, allStateAssms, inWand)
      //      stmts = before ++ stmts ++ after
      val f = c.handleStmt(stmt, statesStack, allStateAssms, duringPackage)
      stmts = f(stmts)
    }
    if (stmts.children.size == 0) {
      assert(assertion = false, "Translation of " + stmt + " is not defined")
    }
    val translation = stmts ::
      (if(duringPackage){
        exchangeAssumesWithBoolean(assumeGoodState, statesStack.head.asInstanceOf[StateRep].boolVar)
      }else{
        assumeGoodState
      }) ::
      Nil

    CommentBlock(comment + s" -- ${stmt.pos}", translation)
  }
}
