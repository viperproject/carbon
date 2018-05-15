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

  type StateRep2 <: stateModule.StateRep

  override def exhale(exps: Seq[(sil.Exp, PartialVerificationError)], havocHeap: Boolean = true, isAssert: Boolean = false
                      , statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false): Stmt = {
    val originalPhaseId = currentPhaseId // needed to get nested exhales (e.g. from unfolding expressions) correct
    val phases = for (phase <- 1 to numberOfPhases) yield {
      currentPhaseId = phase - 1
      val stmts = exps map (e => exhaleConnective(e._1.whenExhaling, e._2, currentPhaseId, havocHeap,
        statesStack, allStateAssms, inWand, isAssert = isAssert))
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
      phases ++ assumptions
    } else {
      beginExhale ++
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
                               isAssert: Boolean = false): Stmt = {
    e match {
      case sil.And(e1, e2) =>
        exhaleConnective(e1, error, phase, havocHeap, statesStack, allStateAssms, inWand) ::
          exhaleConnective(e2, error, phase, havocHeap, statesStack, allStateAssms, inWand) ::
          Nil
      case sil.Implies(e1, e2) =>
        If(translateExp(e1), exhaleConnective(e2, error, phase, havocHeap, statesStack, allStateAssms, inWand), Statements.EmptyStmt)
      case sil.CondExp(c, e1, e2) =>
        If(translateExp(c), exhaleConnective(e1, error, phase, havocHeap, statesStack, allStateAssms, inWand),
          exhaleConnective(e2, error, phase, havocHeap, statesStack, allStateAssms, inWand))
      case sil.Let(declared,boundTo,body) if !body.isPure =>
      {
        val u = env.makeUniquelyNamed(declared) // choose a fresh binder
        env.define(u.localVar)
        Assign(translateLocalVar(u.localVar),translateExp(boundTo)) ::
          exhaleConnective(body.replace(declared.localVar, u.localVar),error,phase, havocHeap, statesStack, allStateAssms, inWand) ::
          {
            env.undefine(u.localVar)
            Nil
          }
      }
      case _ if isInPhase(e, phase) => {
        if(inWand){
          if(phase == 0) {
            // here we create a new state temp (temp: stateRep, init: stmt)
            val StateSetup(tempState, initStmt) = wandModule.createAndSetState(None);
            var exhaleExtStmt = wandModule.exhaleExt(statesStack, tempState, e, allStateAssms)
            val addAssumptions = (statesStack(0).asInstanceOf[StateRep].boolVar := statesStack(0).asInstanceOf[StateRep].boolVar && tempState.boolVar)
            var equateH = equateHeaps(statesStack(0).asInstanceOf[StateRep].state, heapModule)
            var assertTransfer: Stmt =
              if(isAssert)
                stmtModule.translateStmt(sil.Inhale(e)(e.pos, e.info), inWand = true, statesStack = statesStack)
              else
                Nil
            if (!havocHeap)
              initStmt ++ exhaleExtStmt ++ addAssumptions ++ equateH ++ assertTransfer
            else
              initStmt ++ exhaleExtStmt ++ addAssumptions ++ assertTransfer
          }else Nil
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
