// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules.impls

import viper.carbon.modules._
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.verifier.Verifier
import Implicits._
import viper.carbon.modules.components.DefinednessState
import viper.silver.ast.utility.Expressions
import viper.silver.verifier.PartialVerificationError
import viper.silver.verifier.reasons._

/**
 * The default implementation of a [[viper.carbon.modules.ExhaleModule]].
 */
class DefaultExhaleModule(val verifier: Verifier) extends ExhaleModule {

  import verifier._
  import expModule._
  import permModule._
  import heapModule._
  import mainModule._
  import stateModule._

  def name = "Exhale module"

  override def reset = { }

  override def start(): Unit = {
    register(this)
  }

  var nestedExhaleId = 0

  override def exhale(exps: Seq[(sil.Exp, PartialVerificationError, Option[PartialVerificationError])], havocHeap: Boolean = true,
                      isAssert: Boolean = false , statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false): Stmt = {

    nestedExhaleId += 1

    // create a definedness state that matches the state before the exhale
    val wellDefState = stateModule.freshTempStateKeepCurrent(s"ExhaleWellDef${nestedExhaleId - 1}")
    val wellDefStateInitStmt = stateModule.initToCurrentStmt(wellDefState)

    // creating a new temp state if we are inside a package statement
    val curState = stateModule.state
    var initStmtWand: Stmt = Statements.EmptyStmt
    if(insidePackageStmt){
      val StateSetup(tempState, initStmt) = wandModule.createAndSetState(None)
      wandModule.tempCurState = tempState
      initStmtWand = initStmt
    }
    val tempState: StateRep = wandModule.tempCurState.asInstanceOf[StateRep]

    val exhaleStmt = exps map (e =>
        {
          val defStateData =
                DefinednessCheckData(
                  e._3,
                  Some(DefinednessState(() => stateModule.replaceState(wellDefState)))
                )

          exhaleConnective(e._1.whenExhaling, e._2, defStateData, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert = isAssert, currentStateForPackage = tempState)
        }
      )

    val assumptions = MaybeCommentBlock("Free assumptions (exhale module)",
      exps map (e => allFreeAssumptions(e._1)))

    stateModule.replaceState(curState)

    nestedExhaleId -= 1

    if ((exps map (_._1.isPure) forall identity) || !havocHeap || isAssert) {
      // if all expressions are pure, then there is no need for heap copies
      // if this is a translation of an Assert statement, there is also no need for heap copies
      wellDefStateInitStmt ++ initStmtWand ++ exhaleStmt ++ assumptions
    } else {
      beginExhale ++
      wellDefStateInitStmt ++
      initStmtWand ++
        exhaleStmt ++
        assumptions ++
        Comment("Finish exhale") ++
        endExhale
    }

  }

  private def maybeDefCheck(e: sil.Exp, defCheckData: DefinednessCheckData): Stmt = {
    defCheckData.performDefinednessChecks.fold(Statements.EmptyStmt: Stmt)(definednessError => checkDefinedness(e, definednessError, makeChecks = true, Some(defCheckData.definednessStateOpt.get)))
  }


  /**
   * Exhales Viper expression connectives (such as logical and/implication) and forwards the
   * translation of other expressions to the exhale components.
    * @param currentStateForPackage The temporary state connected to current statement being evaluated inside package statement
    *                  Access to the current state is needed during translation of an exhale during packaging a wand
   */
  private def exhaleConnective(e: sil.Exp, error: PartialVerificationError, definednessCheckData: DefinednessCheckData,
                               havocHeap: Boolean = true, statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false,
                               isAssert: Boolean, currentStateForPackage: StateRep): Stmt = {

    // creating union of current state and ops state to be used in translating exps
    val currentState = stateModule.state

    e match {
      case sil.And(e1, e2) =>
        exhaleConnective(e1, error, definednessCheckData, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage) ::
          exhaleConnective(e2, error, definednessCheckData, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage) ::
          Nil
      case sil.Implies(e1, e2) =>
        val defCheck = maybeDefCheck(e1, definednessCheckData)
        val exhaleTranslation : Stmt =
          if (insidePackageStmt) {
            val res = If(wandModule.getCurOpsBoolvar() ==> translateExpInWand(e1), exhaleConnective(e2, error, definednessCheckData, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage), Statements.EmptyStmt)
            val unionStmt = wandModule.updateUnion()
            res ++ unionStmt
          } else {
            If(translateExpInWand(e1),
              exhaleConnective(e2, error, definednessCheckData, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage),
              Statements.EmptyStmt)
          }
        defCheck ++ exhaleTranslation
      case sil.CondExp(c, e1, e2) =>
        val defCheck = maybeDefCheck(c, definednessCheckData)
        val exhaleTranslation : Stmt =
          if(insidePackageStmt) {
            If(wandModule.getCurOpsBoolvar(),
              If(translateExpInWand(c), exhaleConnective(e1, error, definednessCheckData, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage),
                exhaleConnective(e2, error, definednessCheckData, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage)),
              Statements.EmptyStmt) ++
              // The union state should be updated because the union state calculated inside exhaleExt (let's call it state U') is inside the then part of if(c){}
              // and outside the if condition c is not satisfied we still evaluate expressions and check definedness in U' without knowing any assumption about it
            wandModule.updateUnion()
          } else {
            If(translateExpInWand(c), exhaleConnective(e1, error, definednessCheckData, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage),
              exhaleConnective(e2, error, definednessCheckData, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage))
          }
        defCheck ++ exhaleTranslation
      case sil.Let(declared,boundTo,body) if !body.isPure =>
      {
        val defCheck = maybeDefCheck(boundTo, definednessCheckData)
        val u = env.makeUniquelyNamed(declared) // choose a fresh binder
        env.define(u.localVar)
        defCheck ::
        Assign(translateLocalVar(u.localVar),translateExpInWand(boundTo)) ::
          exhaleConnective(body.replace(declared.localVar, u.localVar), error, definednessCheckData, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage) ::
          {
            env.undefine(u.localVar)
            Nil
          }
      }
      case fa@sil.Forall(vars, _, body) if fa.isPure =>
        /* We use a special case for pure quantifiers, because the standard approach of just asserting the pure quantifier
           cannot use the information gained from unfoldings inside the quantifier body (which may be required to
           prove the quantifier). Instead, we invoke exhaleConnective on the quantifier body, which gives exhale components the
           option to gain more information from unfoldings, which can then be used when asserting parts of the quantifier body.
         */
      {
        //We do the definedness check separately
        val defCheck = maybeDefCheck(fa, definednessCheckData)

        val varsFresh = vars.map(v => env.makeUniquelyNamed(v))
        varsFresh.foreach(vFresh => env.define(vFresh.localVar))

        val renamedBody = Expressions.instantiateVariables(body, vars.map(_.localVar), varsFresh.map(_.localVar))

        /* We switch off the definedness checks here, because we do it separately. It may be correct, to not do the
           definedness check separately and instead keep the definedness checks switched on.
         */
        val exhaleStmt : Stmt = exhaleConnective(renamedBody, error, definednessCheckData.copyWhereNoChecksPerformed, havocHeap, statesStackForPackageStmt,
          insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage)

        defCheck ++
        Seqn(Seq (
          NondetIf(Seqn(Seq(exhaleStmt, Assume(FalseLit())))),
          //in the non-deterministic branch we checked the assertion, hence we assume the assertion in the main branch
          Assume(translateExp(e)),
          {
            varsFresh.foreach(vFresh => env.undefine(vFresh.localVar))
            Nil
          }
        ))
      }
      case sil.Unfolding(_, body) if !insidePackageStmt =>
        val defCheck = maybeDefCheck(e, definednessCheckData)

        val definednessCheckDataRec =
          if(definednessCheckData.performDefinednessChecks.isDefined) {
            /**
              * We switch off the definedness checks here, because we do them separately in this case.
              * Moreover, we remove the information on the definedness state to avoid exhale components doing the same work
              * that the definedness components do. This can lead to incompletenesses in cases where the information
              * gained by the definedness components is not available in the exhale context (should not happen frequently in practice).
              */
            DefinednessCheckData(None, None)
          } else {
            definednessCheckData
          }

        val checks = components map (_.exhaleExpBeforeAfter(e, error, definednessCheckDataRec.definednessStateOpt))
        val stmtBefore = checks map (_._1())

        val exhaleBody = exhaleConnective(body, error, definednessCheckDataRec, havocHeap,
          statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage)

        val stmtAfter = checks map (_._2())

        defCheck ++ stmtBefore ++ exhaleBody ++ stmtAfter
      case _ => {
        val defCheck = maybeDefCheck(e, definednessCheckData)

        if(insidePackageStmt) {  // handling exhales during packaging a wand
          // currently having wild cards and 'constraining' expressions are not supported during packaging a wand.
          if(!permModule.getCurrentAbstractReads().isEmpty) {
            sys.error("Abstract reads cannot be used during packaging a wand.")  // AG: To be changed to unsupportedFeatureException
          }

          if(permModule.containsWildCard(e)) {
            sys.error("Wild cards cannot be used during packaging a wand.") // AG: To be changed to unsupportedFeatureException
          }

          val exhaleExtStmt = wandModule.exhaleExt(statesStackForPackageStmt, currentStateForPackage, e, wandModule.getCurOpsBoolvar(), error = error, havocHeap = havocHeap)  // executing the exhale statement
          val addAssumptions = (statesStackForPackageStmt(0).asInstanceOf[StateRep].boolVar := statesStackForPackageStmt(0).asInstanceOf[StateRep].boolVar && currentStateForPackage.boolVar)  // adding needed assumptions to states boolean variables
          val equateHps = wandModule.exchangeAssumesWithBoolean(equateHeaps(statesStackForPackageStmt(0).asInstanceOf[StateRep].state, heapModule), statesStackForPackageStmt(0).asInstanceOf[StateRep].boolVar)
          val assertTransfer: Stmt =  // if it is an assert statement we transfer the permissions from temp state to ops state
            if(isAssert && !e.isPure) {
              val curState = stateModule.state
              stateModule.replaceState(statesStackForPackageStmt(0).asInstanceOf[StateRep].state)
              val stmt: Stmt = wandModule.exhaleExt(currentStateForPackage :: Nil, statesStackForPackageStmt(0).asInstanceOf[StateRep], e, wandModule.getCurOpsBoolvar(), error = error)
              stateModule.replaceState(curState)
              stmt
            }
            else
              Nil
          if (!havocHeap)
            defCheck ++ exhaleExtStmt ++ addAssumptions ++ equateHps ++ assertTransfer
          else
            defCheck ++ exhaleExtStmt ++ addAssumptions ++ assertTransfer
        } else {
          defCheck ++
          /* We propagate the definedness state to the components only if no definedness check was performed to avoid
            exhale components doing the same work as the definedness components do */
            invokeExhaleOnComponents(e, error, definednessCheckData.performDefinednessChecks.fold(None : Option[DefinednessState])(_ => definednessCheckData.definednessStateOpt))
        }
      }
    }
  }

  private def invokeExhaleOnComponents(e: sil.Exp, error: PartialVerificationError, definednessCheckOpt: Option[DefinednessState]) : Stmt = {
    val checks = components map (_.exhaleExpBeforeAfter(e, error, definednessCheckOpt))
    val stmtBefore = checks map (_._1())
    // some implementations may rely on the order of these calls

    val stmtAfter = checks map (_._2())

    stmtBefore ++ stmtAfter
  }

  /**
   * Handles only pure expressions - others will be dealt with by other modules
   */
  override def exhaleExp(e: sil.Exp, error: PartialVerificationError, definednessCheckIncluded: Option[DefinednessState]): Stmt =
  {
    if (e.isPure) {
      e match {
        case _ : sil.Unfolding => Nil //handled by exhaleConnective
        case _ => Assert(translateExp(e), error.dueTo(AssertionFalse(e)))
      }
    } else {
      Nil
    }
  }
}


/**
  * Class to specify definedness information during exhale
  *
  * @param performDefinednessChecks empty if no definedness check must be performed, else contains the corresponding definedness error
  * @param definednessStateOpt Contains the state in which definedness checks should be performed. Must be non-empty if definedness checks
  *                         must be performed. If definedness checks should not be performed, then the definedness state can be used to
  *                         gain additional information. In the latter case, this field may be empty when, for example, the definedness state
  *                         is not tracked.
  */
case class DefinednessCheckData(performDefinednessChecks: Option[PartialVerificationError], definednessStateOpt: Option[DefinednessState])
{

  def copyWhereNoChecksPerformed : DefinednessCheckData  = this.copy(performDefinednessChecks = None)

}