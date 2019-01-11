/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.impls

import viper.carbon.modules._
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.verifier.Verifier
import Implicits._
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

  override def reset = {
    currentPhaseId = -1
  }

  override def start() {
    register(this)
  }

  override def exhale(exps: Seq[(sil.Exp, PartialVerificationError)], havocHeap: Boolean = true, isAssert: Boolean = false
                      , statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false): Stmt = {

    // creating a new temp state if we are inside a package statement
    val curState = stateModule.state
    var initStmtWand: Stmt = Statements.EmptyStmt
    if(insidePackageStmt){
      val StateSetup(tempState, initStmt) = wandModule.createAndSetState(None)
      wandModule.tempCurState = tempState
      initStmtWand = initStmt
    }
    var tempState: StateRep = wandModule.tempCurState.asInstanceOf[StateRep]


    val originalPhaseId = currentPhaseId // needed to get nested exhales (e.g. from unfolding expressions) correct
    val phases = for (phase <- 1 to numberOfPhases) yield {
      currentPhaseId = phase - 1
      val stmts = exps map (e => exhaleConnective(e._1.whenExhaling, e._2, currentPhaseId, havocHeap,
        statesStackForPackageStmt, insidePackageStmt, isAssert = isAssert, currentStateForPackage = tempState))
      if (stmts.children.isEmpty) {
        Statements.EmptyStmt
      } else {

        Comment(s"Phase $phase: ${phaseDescription(currentPhaseId)}") ++ stmts: Stmt
      }
    }
    val assumptions = MaybeCommentBlock("Free assumptions",
      exps map (e => allFreeAssumptions(e._1)))

    currentPhaseId = originalPhaseId
    stateModule.replaceState(curState)

    if ((exps map (_._1.isPure) forall identity) || !havocHeap || isAssert) {
      // if all expressions are pure, then there is no need for heap copies
      // if this is a translation of an Assert statement, there is also no need for heap copies
      initStmtWand ++ phases ++ assumptions
    } else {
      beginExhale ++
      initStmtWand ++
        phases ++
        assumptions ++
        Comment("Finish exhale") ++
        endExhale
    }
  }

  /**
   * Exhales Viper expression connectives (such as logical and/implication) and forwards the
   * translation of other expressions to the exhale components.
    * @param currentStateForPackage The temporary state connected to current statement being evaluated inside package statement
    *                  Access to the current state is needed during translation of an exhale during packaging a wand
   */
  private def exhaleConnective(e: sil.Exp, error: PartialVerificationError, phase: Int, havocHeap: Boolean = true,
                               statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false,
                               isAssert: Boolean , currentStateForPackage: StateRep): Stmt = {

    // creating union of current state and ops state to be used in translating exps
    val currentState = stateModule.state

    e match {
      case sil.And(e1, e2) =>
        exhaleConnective(e1, error, phase, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage) ::
          exhaleConnective(e2, error, phase, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage) ::
          Nil
      case sil.Implies(e1, e2) =>
        if(insidePackageStmt){
          val res = If(wandModule.getCurOpsBoolvar() ==> translateExpInWand(e1), exhaleConnective(e2, error, phase, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage), Statements.EmptyStmt)
          val unionStmt = wandModule.updateUnion()
          res ++ unionStmt
        }
        else
          If(translateExpInWand(e1), exhaleConnective(e2, error, phase, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage), Statements.EmptyStmt)
      case sil.CondExp(c, e1, e2) =>
        if(insidePackageStmt)
          If(wandModule.getCurOpsBoolvar(),
            If(translateExpInWand(c), exhaleConnective(e1, error, phase, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage),
              exhaleConnective(e2, error, phase, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage)),
            Statements.EmptyStmt) ++
            // The union state should be updated because the union state calculated inside exhaleExt (let's call it state U') is inside the then part of if(c){}
            // and outside the if condition c is not satisfied we still evaluate expressions and check definedness in U' without knowing any assumption about it
          wandModule.updateUnion()
        else
          If(translateExpInWand(c), exhaleConnective(e1, error, phase, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage),
            exhaleConnective(e2, error, phase, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage))
      case sil.Let(declared,boundTo,body) if !body.isPure =>
      {
        val u = env.makeUniquelyNamed(declared) // choose a fresh binder
        env.define(u.localVar)
        Assign(translateLocalVar(u.localVar),translateExpInWand(boundTo)) ::
          exhaleConnective(body.replace(declared.localVar, u.localVar),error,phase, havocHeap, statesStackForPackageStmt, insidePackageStmt, isAssert, currentStateForPackage = currentStateForPackage) ::
          {
            env.undefine(u.localVar)
            Nil
          }
      }
      case _ if isInPhase(e, phase) => {
        if(insidePackageStmt){  // handling exhales during packaging a wand
          // currently having wild cards and 'constraining' expressions are not supported during packaging a wand.
          if(!permModule.getCurrentAbstractReads().isEmpty)
            sys.error("Abstract reads cannot be used during packaging a wand.")  // AG: To be changed to unsupportedFeatureException
          else
            if(permModule.containsWildCard(e))
              sys.error("Wild cards cannot be used during packaging a wand.") // AG: To be changed to unsupportedFeatureException
            else
          // This could is called many times in different phases to handle wildcards and constraining,
          //  this code for exhaling inside a magic wand should be called only once (in phase 0, in this case)
            if(phase == 0) {
              var exhaleExtStmt = wandModule.exhaleExt(statesStackForPackageStmt, currentStateForPackage, e, wandModule.getCurOpsBoolvar(), error = error, havocHeap = havocHeap)  // executing the exhale statement
              val addAssumptions = (statesStackForPackageStmt(0).asInstanceOf[StateRep].boolVar := statesStackForPackageStmt(0).asInstanceOf[StateRep].boolVar && currentStateForPackage.boolVar)  // adding needed assumptions to states boolean variables
              var equateHps = wandModule.exchangeAssumesWithBoolean(equateHeaps(statesStackForPackageStmt(0).asInstanceOf[StateRep].state, heapModule), statesStackForPackageStmt(0).asInstanceOf[StateRep].boolVar)
              var assertTransfer: Stmt =  // if it is an assert statement we transfer the permissions from temp state to ops state
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
                exhaleExtStmt ++ addAssumptions ++ equateHps ++ assertTransfer
              else
                exhaleExtStmt ++ addAssumptions ++ assertTransfer
            }else {
              Nil
            }

        }else{
          components map (_.exhaleExp(e, error))
        }
      }
      case _ =>
        Nil // nothing to do in this phase
    }
  }

  var currentPhaseId: Int = -1

  /**
   * Handles only pure expressions - others will be dealt with by other modules
   */
  override def exhaleExp(e: sil.Exp, error: PartialVerificationError): Stmt =
  {
    if (e.isPure) {
      Assert(translateExp(e), error.dueTo(AssertionFalse(e)))
    } else {
      Nil
    }
  }
}
