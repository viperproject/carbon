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
                      , statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false): Stmt = {

    // creating a new temp state if we are inside a package statement
    val curState = stateModule.state
    var tempState: StateRep = null
    var initStmtWand: Stmt = Statements.EmptyStmt
    if(inWand){
      var StateSetup(tt, ii) = wandModule.createAndSetState(None)
      tempState = tt
      initStmtWand = ii
    }


    val originalPhaseId = currentPhaseId // needed to get nested exhales (e.g. from unfolding expressions) correct
    val phases = for (phase <- 1 to numberOfPhases) yield {
      currentPhaseId = phase - 1
      val stmts = exps map (e => exhaleConnective(e._1.whenExhaling, e._2, currentPhaseId, havocHeap,
        statesStack, allStateAssms, inWand, isAssert = isAssert, tempState = tempState))
      if (stmts.children.isEmpty) {
        Statements.EmptyStmt
      } else {
        Comment(s"Phase $phase: ${phaseDescription(currentPhaseId)}") ++ stmts: Stmt
      }
    }
    val assumptions = MaybeCommentBlock("Free assumptions",
      exps map (e => allFreeAssumptions(e._1)))

    currentPhaseId = originalPhaseId

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
   */
  private def exhaleConnective(e: sil.Exp, error: PartialVerificationError, phase: Int, havocHeap: Boolean = true,
                               statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false,
                               isAssert: Boolean , tempState: StateRep): Stmt = {

    // creating union of current state and ops state to be used in translating exps
    val currentState = stateModule.state
    var resultState: StateRep = null
    var unionStmt: Stmt = Statements.EmptyStmt
    if(inWand){
      var StateSetup(tmpResultState, tmpUnionStmt) = wandModule.createAndSetSumState(statesStack.head.asInstanceOf[StateRep].state,
        statesStack.head.asInstanceOf[StateRep].boolVar, allStateAssms)
      resultState = tmpResultState
      unionStmt = tmpUnionStmt ++
        (statesStack.head.asInstanceOf[StateRep].boolVar :=  statesStack.head.asInstanceOf[StateRep].boolVar && resultState.boolVar)
      stateModule.replaceState(currentState)
    }

    e match {
      case sil.And(e1, e2) =>
        exhaleConnective(e1, error, phase, havocHeap, statesStack, allStateAssms, inWand, isAssert, tempState = tempState) ::
          exhaleConnective(e2, error, phase, havocHeap, statesStack, allStateAssms, inWand, isAssert, tempState = tempState) ::
          Nil
      case sil.Implies(e1, e2) =>
        if(inWand)
          unionStmt ++ If(allStateAssms ==> translateExpInWand(e1, statesStack, allStateAssms, inWand, union = true, resultState), exhaleConnective(e2, error, phase, havocHeap, statesStack, allStateAssms, inWand, isAssert, tempState = tempState), Statements.EmptyStmt)
        else
          If(translateExpInWand(e1, statesStack, allStateAssms, inWand), exhaleConnective(e2, error, phase, havocHeap, statesStack, allStateAssms, inWand, isAssert, tempState = tempState), Statements.EmptyStmt)
      case sil.CondExp(c, e1, e2) =>
        if(inWand)
          unionStmt ++ If(allStateAssms ==> translateExpInWand(c, statesStack, allStateAssms, inWand, union = true, resultState), exhaleConnective(e1, error, phase, havocHeap, statesStack, allStateAssms, inWand, isAssert, tempState = tempState),
            exhaleConnective(e2, error, phase, havocHeap, statesStack, allStateAssms, inWand, isAssert, tempState = tempState))
        else
          If(translateExpInWand(c, statesStack, allStateAssms, inWand), exhaleConnective(e1, error, phase, havocHeap, statesStack, allStateAssms, inWand, isAssert, tempState = tempState),
            exhaleConnective(e2, error, phase, havocHeap, statesStack, allStateAssms, inWand, isAssert, tempState = tempState))
      case sil.Let(declared,boundTo,body) if !body.isPure =>
      {
        val u = env.makeUniquelyNamed(declared) // choose a fresh binder
        env.define(u.localVar)
        unionStmt :: Assign(translateLocalVar(u.localVar),translateExpInWand(boundTo, statesStack, allStateAssms, inWand, union = true, resultState)) ::
          exhaleConnective(body.replace(declared.localVar, u.localVar),error,phase, havocHeap, statesStack, allStateAssms, inWand, isAssert, tempState = tempState) ::
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
                  throw new ArrayIndexOutOfBoundsException() // AG: To be changed to unsupportedFeatureException
            else
            if(phase == 0) {
              var exhaleExtStmt = wandModule.exhaleExt(statesStack, tempState, e, allStateAssms, unionState = resultState)  // transferring permissions from stack of states to temp state
              val addAssumptions = (statesStack(0).asInstanceOf[StateRep].boolVar := statesStack(0).asInstanceOf[StateRep].boolVar && tempState.boolVar)  // adding all assumptions of temp.bool to ops.bool
              var equateHps = wandModule.exchangeAssumesWithBoolean(equateHeaps(statesStack(0).asInstanceOf[StateRep].state, heapModule), statesStack(0).asInstanceOf[StateRep].boolVar)  // equating ops and temp heaps
              var assertTransfer: Stmt =  // if it is an assert statement we transfer the permissions from temp state to ops state
                if(isAssert && !e.isPure) {
                  val curState = stateModule.state
                  stateModule.replaceState(statesStack(0).asInstanceOf[StateRep].state)
                  val stmt: Stmt = wandModule.exhaleExt(tempState :: Nil, statesStack(0).asInstanceOf[StateRep], e, allStateAssms, unionState = tempState)
                  stateModule.replaceState(curState)
                  stmt
                }
                else
                  Nil
              if (!havocHeap)
                unionStmt ++ exhaleExtStmt ++ addAssumptions ++ equateHps ++ assertTransfer
              else
                unionStmt ++ exhaleExtStmt ++ addAssumptions ++ assertTransfer
            }else {
              Nil
            }

        }else{
          components map (_.exhaleExp(e, error, allStateAssms))
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
  override def exhaleExp(e: sil.Exp, error: PartialVerificationError, allStateAssms: Exp = TrueLit()): Stmt =
  {
    if (e.isPure) {
      Assert(allStateAssms ==> translateExp(e), error.dueTo(AssertionFalse(e)))
    } else {
      Nil
    }
  }
}
