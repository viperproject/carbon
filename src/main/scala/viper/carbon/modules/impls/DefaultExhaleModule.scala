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
                      , statesStack: List[Any] = null, inWand: Boolean = false): Stmt = {

    // creating a new temp state if we are inside a package statement
    val curState = stateModule.state
    var initStmtWand: Stmt = Statements.EmptyStmt
    if(inWand){
      val StateSetup(tempState, initStmt) = wandModule.createAndSetState(None)
      wandModule.tempCurState = tempState
      initStmtWand = initStmt
    }
    var tempState: StateRep = wandModule.tempCurState.asInstanceOf[StateRep]


    val originalPhaseId = currentPhaseId // needed to get nested exhales (e.g. from unfolding expressions) correct
    val phases = for (phase <- 1 to numberOfPhases) yield {
      currentPhaseId = phase - 1
      val stmts = exps map (e => exhaleConnective(e._1.whenExhaling, e._2, currentPhaseId, havocHeap,
        statesStack, inWand, isAssert = isAssert, tempState = tempState))
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
    * @param tempState The temporary state connected to current statement being evaluated inside package statement
   */
  private def exhaleConnective(e: sil.Exp, error: PartialVerificationError, phase: Int, havocHeap: Boolean = true,
                               statesStack: List[Any] = null, inWand: Boolean = false,
                               isAssert: Boolean , tempState: StateRep): Stmt = {

    // creating union of current state and ops state to be used in translating exps
    val currentState = stateModule.state

    e match {
      case sil.And(e1, e2) =>
        exhaleConnective(e1, error, phase, havocHeap, statesStack, inWand, isAssert, tempState = tempState) ::
          exhaleConnective(e2, error, phase, havocHeap, statesStack, inWand, isAssert, tempState = tempState) ::
          Nil
      case sil.Implies(e1, e2) =>
        if(inWand){
          val res = If(wandModule.getCurOpsBoolvar() ==> translateExpInWand(e1), exhaleConnective(e2, error, phase, havocHeap, statesStack, inWand, isAssert, tempState = tempState), Statements.EmptyStmt)
          val unionStmt = wandModule.updateUnion()
          res ++ unionStmt
        }
        else
          If(translateExpInWand(e1), exhaleConnective(e2, error, phase, havocHeap, statesStack, inWand, isAssert, tempState = tempState), Statements.EmptyStmt)
      case sil.CondExp(c, e1, e2) =>
        if(inWand)
          If(wandModule.getCurOpsBoolvar(),
            If(translateExpInWand(c), exhaleConnective(e1, error, phase, havocHeap, statesStack, inWand, isAssert, tempState = tempState),
              exhaleConnective(e2, error, phase, havocHeap, statesStack, inWand, isAssert, tempState = tempState)),
            Statements.EmptyStmt) ++
            // The union state should be updated because the union state calculated inside exhaleExt (let's call it state U') is inside the then part of if(c){}
            // and outside the if condition c is not satisfied we still evaluate expressions and check definedness in U' without knowing any assumption about it
          wandModule.updateUnion()
        else
          If(translateExpInWand(c), exhaleConnective(e1, error, phase, havocHeap, statesStack, inWand, isAssert, tempState = tempState),
            exhaleConnective(e2, error, phase, havocHeap, statesStack, inWand, isAssert, tempState = tempState))
      case sil.Let(declared,boundTo,body) if !body.isPure =>
      {
        val u = env.makeUniquelyNamed(declared) // choose a fresh binder
        env.define(u.localVar)
        Assign(translateLocalVar(u.localVar),translateExpInWand(boundTo)) ::
          exhaleConnective(body.replace(declared.localVar, u.localVar),error,phase, havocHeap, statesStack, inWand, isAssert, tempState = tempState) ::
          {
            env.undefine(u.localVar)
            Nil
          }
      }
      case _ if isInPhase(e, phase) => {
        if(inWand){
          if(!permModule.getCurrentAbstractReads().isEmpty)
            throw new RuntimeException()  // AG: To be changed to unsupportedFeatureException
          else
            if(permModule.containsWildCard(e))
                  throw new RuntimeException() // AG: To be changed to unsupportedFeatureException
            else
          // currently having wild cards and 'constraining' expressions are not supported during packaging a wand.
          // This could is called many times in different phases to handle wildcards and constraining,
          //  this code for exhaling inside a magic wand should be called only once (in phase 0, in this case)
            if(phase == 0) {
              var exhaleExtStmt = wandModule.exhaleExt(statesStack, tempState, e, wandModule.getCurOpsBoolvar(), error = error, havocHeap = havocHeap)  // transferring permissions from stack of states to temp state
              val addAssumptions = (statesStack(0).asInstanceOf[StateRep].boolVar := statesStack(0).asInstanceOf[StateRep].boolVar && tempState.boolVar)  // adding all assumptions of temp.bool to ops.bool
              var equateHps = wandModule.exchangeAssumesWithBoolean(equateHeaps(statesStack(0).asInstanceOf[StateRep].state, heapModule), statesStack(0).asInstanceOf[StateRep].boolVar)  // equating ops and temp heaps
              var assertTransfer: Stmt =  // if it is an assert statement we transfer the permissions from temp state to ops state
                if(isAssert && !e.isPure) {
                  val curState = stateModule.state
                  stateModule.replaceState(statesStack(0).asInstanceOf[StateRep].state)
                  val stmt: Stmt = wandModule.exhaleExt(tempState :: Nil, statesStack(0).asInstanceOf[StateRep], e, wandModule.getCurOpsBoolvar(), error = error)
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
