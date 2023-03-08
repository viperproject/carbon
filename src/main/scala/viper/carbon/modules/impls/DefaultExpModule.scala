// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules.impls

import viper.carbon.boogie.Implicits._
import viper.carbon.boogie._
import viper.carbon.modules.components.DefinednessComponent
import viper.carbon.modules.{ExpModule, StatelessComponent}
import viper.carbon.verifier.Verifier
import viper.silver.ast.utility.Expressions
import viper.silver.ast.{LocationAccess, MagicWand, PredicateAccess, Ref}
import viper.silver.verifier.{PartialVerificationError, reasons}
import viper.silver.{ast => sil}

/**
 * The default implementation of [[viper.carbon.modules.ExpModule]].
 */
class DefaultExpModule(val verifier: Verifier) extends ExpModule with DefinednessComponent with StatelessComponent {

  import verifier._
  import domainModule._
  import exhaleModule._
  import funcPredModule._
  import heapModule._
  import inhaleModule._
  import mainModule._
  import mapModule._
  import permModule._
  import seqModule._
  import setModule._
  import stateModule._

  override def start(): Unit = {
    register(this)
  }

  def name = "Expression module"

  override def translateExpInWand(e: sil.Exp): Exp = {
    val duringPackageStmt = wandModule.nestingDepth > 0
    if(duringPackageStmt){
      val oldCurState = stateModule.state
      stateModule.replaceState(wandModule.UNIONState.asInstanceOf[StateRep].state)  // state in which 'e' is evaluated

      val stmt = translateExp(e)

      stateModule.replaceState(oldCurState)

      stmt
    }else{
      translateExp(e)
    }
  }

  override def translateExp(e: sil.Exp): Exp = {
    e match {
      case sil.IntLit(i) =>
        IntLit(i)
      case sil.BoolLit(b) =>
        BoolLit(b)
      case sil.NullLit() =>
        translateNull
      case l@sil.LocalVar(_, _) =>
        translateLocalVar(l)
      case r@sil.Result(_) =>
        translateResult(r)
      case f@sil.FieldAccess(_, _) =>
        translateLocationAccess(f)
      case sil.InhaleExhaleExp(_, _) =>
        sys.error("should not occur here (either, we inhale or exhale this expression, in which case whenInhaling/whenExhaling should be used, or the expression is not allowed to occur.")
      case p@sil.PredicateAccess(_, _) =>
        translateLocationAccess(p)
      case h: sil.HintExp => translateExp(h.body)
      case sil.Old(exp) =>
        val prevState = stateModule.state
        stateModule.replaceState(stateModule.oldState)
        val res = translateExp(exp)
        stateModule.replaceState(prevState)
        res
      case sil.LabelledOld(exp, oldLabel) =>
        var findLabel = oldLabel
        if(findLabel.equals("lhs"))
          findLabel = findLabel+wandModule.getActiveLhs()
        val prevState = stateModule.state
        val labelState = LabelHelper.getLabelState[stateModule.StateSnapshot](
          findLabel,
          stateModule.freshTempStateKeepCurrent,
          stateModule.stateRepositoryGet, stateModule.stateRepositoryPut)
        stateModule.replaceState(labelState)
        val res = translateExp(exp)
        stateModule.replaceState(prevState)
        res
      case sil.Let(lvardecl, exp, body) =>
        val translatedExp = translateExp(exp) // expression to bind "v" to
      val v = env.makeUniquelyNamed(lvardecl) // choose a fresh "v" binder
        env.define(v.localVar)
        val translatedBody = translateExp(Expressions.instantiateVariables(body, Seq(lvardecl), Seq(v.localVar), env.allDefinedNames(program))) // translate body with "v" in place of bound variable
      val substitutedBody = translatedBody.replace(env.get(v.localVar), translatedExp) // now replace all "v"s with expression. Doing this after translation avoids constructs such as heap-dependant expressions getting reevaluated after substitution in the wrong heaps (e.g. if substituted into an "old" expression).
        env.undefine(v.localVar)
        substitutedBody
      case sil.CondExp(cond, thn, els) =>
        CondExp(translateExp(cond), translateExp(thn), translateExp(els))
      case q@sil.Exists(vars, triggers, exp) => {
        // alpha renaming, to avoid clashes in context
        val renamedVars: Seq[sil.LocalVarDecl] = vars map (v => {
          val v1 = env.makeUniquelyNamed(v); env.define(v1.localVar); v1
        });
        val renaming = (e: sil.Exp) => Expressions.instantiateVariables(e, (vars map (_.localVar)), renamedVars map (_.localVar))
        val ts : Seq[Trigger] = (triggers map
          (t => (funcPredModule.toExpressionsUsedInTriggers(t.exps map (e => translateExp(renaming(e)))))
            map (Trigger(_)) // build a trigger for each sequence element returned (in general, one original trigger can yield multiple alternative new triggers)
            )).flatten
        val weight = q.info match {
          case sil.WeightedQuantifier(value) => Some(value)
          case _ => None
        }
        val res = Exists(renamedVars map translateLocalVarDecl, ts, translateExp(renaming(exp)), weight)
        renamedVars map (v => env.undefine(v.localVar))
        res
      }
      case q@sil.Forall(vars, triggers, exp) => {
        // alpha renaming, to avoid clashes in context
        val renamedVars: Seq[sil.LocalVarDecl] = vars map (v => {
          val v1 = env.makeUniquelyNamed(v); env.define(v1.localVar); v1
        });
        val renaming = (e: sil.Exp) => Expressions.instantiateVariables(e, (vars map (_.localVar)), renamedVars map (_.localVar))
        val ts : Seq[Trigger] = (triggers map
          (t => (funcPredModule.toExpressionsUsedInTriggers(t.exps map (e => translateExp(renaming(e)))))
            map (Trigger(_)) // build a trigger for each sequence element returned (in general, one original trigger can yield multiple alternative new triggers)
            )).flatten
        val weight = q.info match {
          case sil.WeightedQuantifier(value) => Some(value)
          case _ => None
        }
        val res = Forall(renamedVars map translateLocalVarDecl, ts, translateExp(renaming(exp)), Nil, weight)
        renamedVars map (v => env.undefine(v.localVar))
        res
      }
      case sil.ForPerm(variables, accessRes, body) => {

        val variable = variables.head

        if (variables.length != 1) sys.error("Carbon only supports a single quantified variable in forperm, see Carbon issue #243")
        if (variable.typ != Ref) sys.error("Carbon only supports Ref type in forperm, see Carbon issue #243")
        accessRes match {
          case _: MagicWand => sys.error("Carbon does not support magic wands in forperm, see Carbon issue #243")
          case p: PredicateAccess => if (p.loc(program).formalArgs.length != 1) sys.error("Carbon only supports predicates with a single argument in forperm, see Carbon issue #243")
          case _ =>
        }

        val locations = Seq(accessRes.asInstanceOf[LocationAccess].loc(program))

        // alpha renaming, to avoid clashes in context
        val renamedVar: sil.LocalVarDecl = {
          val v1 = env.makeUniquelyNamed(variable); env.define(v1.localVar); v1
        }
        val renaming = (e: sil.Exp) => Expressions.instantiateVariables(e, Seq(variable.localVar), Seq(renamedVar.localVar))
        // val ts = triggers map (t => Trigger(t.exps map {e => verifier.funcPredModule.toTriggers(translateExp(renaming(e)))} // no triggers yet?
        val perLocFilter: sil.Location => (Exp, Trigger) = loc => {
          val locAccess: LocationAccess = loc match {
            case f: sil.Field => sil.FieldAccess(renamedVar.localVar, f)(loc.pos, loc.info)
            case p: sil.Predicate => sil.PredicateAccess(Seq(renamedVar.localVar), p)(loc.pos, loc.info, loc.errT)
          }
          (hasDirectPerm(locAccess), Trigger(permissionLookup(locAccess)))
        }
        val filter = locations.foldLeft[(Exp, Seq[Trigger])](BoolLit(false), Seq())((soFar, loc) => soFar match {
          case (exp, triggers) =>
            perLocFilter(loc) match {
              case (newExp, newTrigger) => (BinExp(exp, Or, newExp), triggers ++ Seq(newTrigger))
            }
        })

        val res = Forall(translateLocalVarDecl(renamedVar), filter._2, // no triggers yet :(
          BinExp(filter._1, Implies, translateExp(renaming(body))))
        env.undefine(renamedVar.localVar)
        res
      }
      case sil.WildcardPerm() =>
        translatePerm(e)
      case sil.FullPerm() =>
        translatePerm(e)
      case sil.NoPerm() =>
        translatePerm(e)
      case sil.EpsilonPerm() =>
        translatePerm(e)
      case sil.PermMinus(_) =>
        translatePerm(e)
      case sil.CurrentPerm(_) =>
        translatePerm(e)
      case sil.FractionalPerm(_, _) =>
        translatePerm(e)
      case sil.AccessPredicate(_, _) =>
        sys.error("not handled by expression module")
      case sil.EqCmp(left, right) =>
        left.typ match {
          case _: sil.SeqType =>
            translateSeqExp(e)
          case _: sil.SetType =>
            translateSetExp(e)
          case _: sil.MultisetType =>
            translateSetExp(e)
          case _: sil.MapType =>
            translateMapExp(e)
          case x if x == sil.Perm =>
            translatePermComparison(e)
          case _ =>
            BinExp(translateExp(left), EqCmp, translateExp(right))
        }
      case sil.NeCmp(left, right) =>
        left.typ match {
          case _: sil.SeqType =>
            translateSeqExp(e)
          case _: sil.SetType =>
            translateSetExp(e)
          case _: sil.MultisetType =>
            translateSetExp(e)
          case _: sil.MapType =>
            translateMapExp(e)
          case x if x == sil.Perm =>
            translatePermComparison(e)
          case _ =>
            BinExp(translateExp(left), NeCmp, translateExp(right))
        }
      case sil.DomainBinExp(_, sil.PermGeOp, _) |
           sil.DomainBinExp(_, sil.PermGtOp, _) |
           sil.DomainBinExp(_, sil.PermLeOp, _) |
           sil.DomainBinExp(_, sil.PermLtOp, _) =>
        translatePermComparison(e)
      case sil.DomainBinExp(_, sil.PermAddOp, _) |
           sil.DomainBinExp(_, sil.PermMulOp, _) |
           sil.DomainBinExp(_, sil.PermSubOp, _) |
           sil.DomainBinExp(_, sil.IntPermMulOp, _) |
           sil.DomainBinExp(_, sil.FracOp, _) |
           sil.DomainBinExp(_, sil.PermDivOp, _) =>
        translatePerm(e)
      case sil.DomainBinExp(left, op, right) =>
        val bop = op match {
          case sil.OrOp => Or
          case sil.LeOp => LeCmp
          case sil.LtOp => LtCmp
          case sil.GeOp => GeCmp
          case sil.GtOp => GtCmp
          case sil.AddOp => Add
          case sil.SubOp => Sub
          case sil.DivOp => IntDiv
          case sil.ModOp => Mod
          case sil.MulOp => Mul
          case sil.AndOp => And
          case sil.ImpliesOp => Implies
          case _ =>
            sys.error("Expression translation did not match any cases (should be handled before reaching translateExp code)" + e.getClass())
        }
        BinExp(translateExp(left), bop, translateExp(right))
      case sil.Minus(exp) =>
        UnExp(Minus, translateExp(exp))
      case sil.Not(exp) =>
        UnExp(Not, translateExp(exp))
      case fa@sil.FuncApp(_, _) =>
        translateFuncApp(fa)
      case fa@sil.DomainFuncApp(_, _, _) =>
        translateDomainFuncApp(fa)
      case fa@sil.BackendFuncApp(_, _) =>
        translateBackendFuncApp(fa)

      case seqExp@sil.EmptySeq(_) =>
        translateSeqExp(seqExp)
      case seqExp@sil.ExplicitSeq(_) =>
        translateSeqExp(seqExp)
      case seqExp@sil.RangeSeq(_, _) =>
        translateSeqExp(seqExp)
      case seqExp@sil.SeqAppend(_, _) =>
        translateSeqExp(seqExp)
      case seqExp@sil.SeqIndex(_, _) =>
        translateSeqExp(seqExp)
      case seqExp@sil.SeqTake(_, _) =>
        translateSeqExp(seqExp)
      case seqExp@sil.SeqDrop(_, _) =>
        translateSeqExp(seqExp)
      case seqExp@sil.SeqContains(_, _) =>
        translateSeqExp(seqExp)
      case seqExp@sil.SeqUpdate(_, _, _) =>
        translateSeqExp(seqExp)
      case seqExp@sil.SeqLength(_) =>
        translateSeqExp(seqExp)

      case setExp@sil.EmptySet(_) => translateSetExp(setExp)
      case setExp@sil.ExplicitSet(_) => translateSetExp(setExp)
      case setExp@sil.EmptyMultiset(_) => translateSetExp(setExp)
      case setExp@sil.ExplicitMultiset(_) => translateSetExp(setExp)
      case setExp@sil.AnySetUnion(_, _) => translateSetExp(setExp)
      case setExp@sil.AnySetIntersection(_, _) => translateSetExp(setExp)
      case setExp@sil.AnySetSubset(_, _) => translateSetExp(setExp)
      case setExp@sil.AnySetMinus(_, _) => translateSetExp(setExp)
      case setExp@sil.AnySetContains(_, _) => translateSetExp(setExp)
      case setExp@sil.AnySetCardinality(_) => translateSetExp(setExp)

      case mapExp: sil.EmptyMap => translateMapExp(mapExp)
      case mapExp: sil.ExplicitMap => translateMapExp(mapExp)
      case mapExp: sil.Maplet => translateMapExp(mapExp)
      case mapExp: sil.MapCardinality => translateMapExp(mapExp)
      case mapExp: sil.MapContains => translateMapExp(mapExp)
      case mapExp: sil.MapDomain => translateMapExp(mapExp)
      case mapExp: sil.MapRange => translateMapExp(mapExp)
      case mapExp: sil.MapLookup => translateMapExp(mapExp)
      case mapExp: sil.MapUpdate => translateMapExp(mapExp)

      case _ => sys.error("Viper expression didn't match any existing case.")
    }
  }

  override def translateLocalVar(l: sil.LocalVar): LocalVar = {
    env.get(l)
  }

  override def simplePartialCheckDefinednessAfter(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean): Stmt = {

    val stmt: Stmt = (if (makeChecks)
      e match {
        case sil.Div(_, b) =>
            Assert(translateExp(b) !== IntLit(0), error.dueTo(reasons.DivisionByZero(b)))
        case sil.Mod(_, b) =>
            Assert(translateExp(b) !== IntLit(0), error.dueTo(reasons.DivisionByZero(b)))
        case sil.FractionalPerm(_, b) =>
            Assert(translateExp(b) !== IntLit(0), error.dueTo(reasons.DivisionByZero(b)))
        case _ => Nil
      }
    else Nil)

    stmt
  }

  override def checkDefinedness(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean,
                                duringPackageStmt: Boolean = false, ignoreIfInWand: Boolean = false): Stmt = {

    if(duringPackageStmt && ignoreIfInWand)  // ignore the check
      return Statements.EmptyStmt

    val oldCurState = stateModule.state
    if(duringPackageStmt) {
      stateModule.replaceState(wandModule.UNIONState.asInstanceOf[StateRep].state)
    }

    val stmt =
      MaybeCommentBlock(s"Check definedness of $e", checkDefinednessImpl(e, error, makeChecks = makeChecks))

    if(duringPackageStmt) {
      stateModule.replaceState(oldCurState)
      If(wandModule.getCurOpsBoolvar(), stmt, Statements.EmptyStmt)
    }else stmt
  }

  private def checkDefinednessImpl(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean): Stmt = {
    e match {
      case sil.And(e1, e2) =>
        checkDefinednessImpl(e1, error, makeChecks = makeChecks) ::
          If(translateExp(Expressions.asBooleanExp(e1)), checkDefinednessImpl(e2, error, makeChecks = makeChecks), Statements.EmptyStmt) ::
          Nil
      case sil.Implies(e1, e2) =>
        checkDefinednessImpl(e1, error, makeChecks = makeChecks) ::
          If(translateExp(e1), checkDefinednessImpl(e2, error, makeChecks = makeChecks), Statements.EmptyStmt) ::
          Nil
      case sil.CondExp(c, e1, e2) =>
        checkDefinednessImpl(c, error, makeChecks = makeChecks) ::
          If(translateExp(c), checkDefinednessImpl(e1, error, makeChecks = makeChecks), checkDefinednessImpl(e2, error, makeChecks = makeChecks)) ::
          Nil
      case sil.Or(e1, e2) =>
        checkDefinednessImpl(e1, error, makeChecks = makeChecks) :: // short-circuiting evaluation:
          If(UnExp(Not, translateExp(e1)), checkDefinednessImpl(e2, error, makeChecks = makeChecks), Statements.EmptyStmt) ::
          Nil
      case sil.Asserting(assertion, e) =>
        checkDefinedness(assertion, error, makeChecks = makeChecks) ::
          NondetIf(
            MaybeComment("Exhale assertion of asserting", exhale(Seq((assertion, error)))) ++
              MaybeComment("Stop execution", Assume(FalseLit()))
            , Nil) ::
          checkDefinedness(e, error, makeChecks = makeChecks) ::
          Nil
      case w@sil.MagicWand(_, _) =>
        checkDefinednessWand(w, error, makeChecks = makeChecks)
      case sil.Let(v, e, body) =>
        checkDefinednessImpl(e, error, makeChecks = makeChecks) ::
        {
          val u = env.makeUniquelyNamed(v) // choose a fresh "v" binder
          env.define(u.localVar)
          Assign(translateLocalVar(u.localVar),translateExp(e)) ::
          checkDefinednessImpl(body.replace(v.localVar, u.localVar), error, makeChecks = makeChecks) ::
            {
              env.undefine(u.localVar)
              Nil
            }
        }
      case _ =>
        def translate(e: sil.Exp): Seqn = {
          val checks = components map (_.partialCheckDefinedness(e, error, makeChecks = makeChecks))
          val stmt = checks map (_._1())

          // AS: note that some implementations of the definedness checks rely on the order of these calls (i.e. parent nodes are checked before children, and children *are* always checked after parents.
          val stmt2 = for (sub <- subexpressionsForDefinedness(e)) yield {
            checkDefinednessImpl(sub, error, makeChecks = makeChecks)
          }
          val stmt3 = checks map (_._2())

          e match {
            case sil.MagicWand(_, _) =>
              sys.error("wand subnodes:" + e.subnodes.toString() +
                "stmt:" + stmt.toString() +
                "stmt2:" + stmt2.toString() +
                "stmt3:" + stmt3.toString())
            case _ => Nil
          }

          stmt ++ stmt2 ++ stmt3 ++
            MaybeCommentBlock("Free assumptions (exp module)", allFreeAssumptions(e))
        }

        if (e.isInstanceOf[sil.QuantifiedExp]) {
          val orig_vars = e.asInstanceOf[sil.QuantifiedExp].variables
          val bound_vars = orig_vars.map(v => env.makeUniquelyNamed(v))
          bound_vars map (v => env.define(v.localVar))
          val res = if (e.isInstanceOf[sil.ForPerm]) {
            val eAsForallRef = Expressions.renameVariables(e, orig_vars.map(_.localVar), bound_vars.map(_.localVar)).asInstanceOf[sil.ForPerm]

            if (eAsForallRef.variables.length != 1) sys.error("Carbon only supports a single quantified variable in forperm, see Carbon issue #243")
            if (eAsForallRef.variables.head.typ != Ref) sys.error("Carbon only supports Ref type in forperm, see Carbon issue #243")
            eAsForallRef.resource match {
              case _: MagicWand => sys.error("Carbon does not support magic wands in forperm, see Carbon issue #243")
              case p: PredicateAccess => if (p.loc(program).formalArgs.length != 1) sys.error("Carbon only supports predicates with a single argument in forperm, see Carbon issue #243")
              case _ =>
            }

            val filter: Exp = hasDirectPerm(eAsForallRef.resource.asInstanceOf[LocationAccess])

            handleQuantifiedLocals(bound_vars, If(filter, translate(eAsForallRef), Nil))
          } else handleQuantifiedLocals(bound_vars, translate(Expressions.renameVariables(e, orig_vars.map(_.localVar), bound_vars.map(_.localVar))))
          bound_vars map (v => env.undefine(v.localVar))
          res
        } else e match {
          case sil.Old(_) =>
            val prevState = stateModule.state
            stateModule.replaceState(stateModule.oldState)
            val res = translate(e)
            stateModule.replaceState(prevState)
            res
          case sil.LabelledOld(_, oldLabel) =>
            var findLabel = oldLabel
            if(findLabel.equals("lhs"))
              findLabel = "lhs"+wandModule.getActiveLhs()
            val prevState = stateModule.state
            val labelState = LabelHelper.getLabelState[stateModule.StateSnapshot](
              findLabel,
              stateModule.freshTempStateKeepCurrent,
              stateModule.stateRepositoryGet, stateModule.stateRepositoryPut)
            stateModule.replaceState(labelState)
            val res = translate(e)
            stateModule.replaceState(prevState)
            res
          case _ =>
            translate(e)
        }
    }
  }

  /***
    * Returns subexpressions that are relevant for definedness checks
    */
  private def subexpressionsForDefinedness(e: sil.Exp) : Seq[sil.Exp] = {
    e match {
      case sil.AccessPredicate(res : sil.LocationAccess, perm) => res.subExps ++ Seq(perm)
      case sil.CurrentPerm(res: sil.LocationAccess) => res.subExps
      case _ => e.subExps
    }
  }

  /**
    * checks self-framedness of both sides of wand
    * GP: maybe should "MagicWandNotWellFormed" error
    */
  private def checkDefinednessWand(e: sil.MagicWand, error: PartialVerificationError, makeChecks: Boolean): Stmt = {
    val (initStmtLHS, curState): (Stmt, stateModule.StateSnapshot) = stateModule.freshEmptyState("WandDefLHS", true)
    val defStateLHS = stateModule.state
    val (initStmtRHS, _): (Stmt, stateModule.StateSnapshot) = stateModule.freshEmptyState("WandDefRHS", true)
    val defStateRHS = stateModule.state

    stateModule.replaceState(defStateLHS)
    val lhs = initStmtLHS ++ inhaleWithDefinednessCheck(e.left, error)
    val lhsID = wandModule.getNewLhsID() // identifier for the lhs of the wand to be referred to later when 'old(lhs)' is used
    val defineLHS = stmtModule.translateStmt(sil.Label("lhs"+lhsID, Nil)(e.pos, e.info))
    wandModule.pushToActiveWandsStack(lhsID)
    stateModule.replaceState(defStateRHS)
    val rhs = initStmtRHS ++ inhaleWithDefinednessCheck(e.right, error)
    wandModule.popFromActiveWandsStack()
    stateModule.replaceState(curState)
    NondetIf(lhs ++ defineLHS ++ rhs ++ Assume(FalseLit()))
  }

  def handleQuantifiedLocals(vars: Seq[sil.LocalVarDecl], res: Stmt): Stmt = {
    // introduce local variables for the variables in quantifications. we do this by first check
    // definedness without worrying about missing variable declarations, and then replace all of them
    // with fresh variables.
    val namespace = verifier.freshNamespace("exp.quantifier")
    val newVars = vars map (x => (translateLocalVar(x.localVar),
      // we use a fresh namespace to make sure we get fresh variables
      Identifier(x.name)(namespace)
      ))
    NondetIf(Seqn(Seq(Transformer.transform(res, {
      case v@LocalVar(name, _) =>
        newVars.find(x => (name == x._1.name)) match {
          case None => v // no change
          case Some((x, xb)) =>
            // use the new variable
            LocalVar(xb, x.typ)
        }
    })(),Assume(FalseLit()))))
  }

  def checkDefinednessOfSpecAndExhale(e: sil.Exp, definednessError: PartialVerificationError, exhaleError: PartialVerificationError
                                               , statesStack: List[Any] = null, duringPackageStmt: Boolean = false): Stmt = {

    val stmt =
      e match {
      case sil.And(e1, e2) =>
        checkDefinednessOfSpecAndExhale(e1, definednessError, exhaleError, statesStack, duringPackageStmt) ::
          checkDefinednessOfSpecAndExhale(e2, definednessError, exhaleError, statesStack, duringPackageStmt) ::
          Nil
      case sil.Implies(e1, e2) =>
        checkDefinedness(e1, definednessError) ++
          If(translateExp(e1), checkDefinednessOfSpecAndExhale(e2, definednessError, exhaleError, statesStack, duringPackageStmt), Statements.EmptyStmt)
      case sil.CondExp(c, e1, e2) =>
        checkDefinedness(c, definednessError) ++
          If(translateExp(c),
            checkDefinednessOfSpecAndExhale(e1, definednessError, exhaleError, statesStack, duringPackageStmt),
            checkDefinednessOfSpecAndExhale(e2, definednessError, exhaleError, statesStack, duringPackageStmt))
      case sil.Let(v, exp, body) =>
        checkDefinedness(exp, definednessError, true) ::
          {
            val u = env.makeUniquelyNamed(v) // choose a fresh "v" binder
            env.define(u.localVar)
            Assign(translateLocalVar(u.localVar),translateExp(exp)) ::
              checkDefinednessOfSpecAndExhale(body.replace(v.localVar, u.localVar), definednessError, exhaleError) ::
              {
                env.undefine(u.localVar)
                Nil
              }
          }//      case fa@sil.Forall(vars, triggers, expr) => // NOTE: there's no need for a special case for QPs, since these are desugared, introducing conjunctions
      case _ =>
        checkDefinedness(e, definednessError) ++
          exhale(Seq((e, exhaleError)))
    }

    if(duringPackageStmt) {
      If(wandModule.getCurOpsBoolvar(), stmt, Statements.EmptyStmt)
    }else stmt
  }

  override def allFreeAssumptions(e: sil.Exp): Stmt = {
    def translate: Seqn = {
      val stmt = components map (_.freeAssumptions(e))
      /**
       * Generally if e' is a subexpression of e then whenever e is inhaled/exhaled then any assumption that  can be
       * made for free if e' is inhaled/exhaled is also free.
       * If e is a magic wand then this is not true since what is inhaled is just the wand as a complete entity,
       * no assumptions can be made on the left and right hand side or their subexpressions as they contain assertions
       * which are only exhaled/inhaled when the wand is applied.
       */
      val stmt2 =
        e match {
          case sil.MagicWand(_,_) => Nil
          case sil.Forall(_,_,_) => Nil
          case sil.Exists(_,_,_) => Nil
          case sil.Let(v, e, body) => {
            val u = env.makeUniquelyNamed(v) // choose a fresh "v" binder
            env.define(u.localVar)
            val stmts = Assign(translateLocalVar(u.localVar),translateExp(e)) ++ allFreeAssumptions(body.replace(v.localVar,u.localVar))
            env.undefine(u.localVar)
            stmts
          }
          case _ =>
            for (sub <- e.subnodes if sub.isInstanceOf[sil.Exp]) yield {
              allFreeAssumptions(sub.asInstanceOf[sil.Exp])
            }
        }
      stmt ++ stmt2
    }
    if (e.isInstanceOf[sil.Old]) {
      val prevState = stateModule.state
      stateModule.replaceState(stateModule.oldState)
      val res = translate
      stateModule.replaceState(prevState)
      res
    } else {
      translate
    }
  }
}
