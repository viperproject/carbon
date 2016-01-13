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

  def name = "Exhale module"

  override def reset = {
    currentPhaseId = -1
  }

  override def start() {
    register(this)
  }

  override def exhale(exps: Seq[(sil.Exp, PartialVerificationError)], havocHeap: Boolean = true): Stmt = {
    val phases = for (phase <- 1 to numberOfPhases) yield {
      currentPhaseId = phase - 1
      val stmts = exps map (e => exhaleConnective(e._1.whenExhaling, e._2, currentPhaseId))
      if (stmts.children.isEmpty) {
        Statements.EmptyStmt
      } else {
        Comment(s"Phase $phase: ${phaseDescription(currentPhaseId)}") ++ stmts: Stmt
      }
    }
    val assumptions = MaybeCommentBlock("Free assumptions",
      exps map (e => allFreeAssumptions(e._1)))
    if ((exps map (_._1.isPure) forall identity) || !havocHeap) {
      // if all expressions are pure, then there is no need for heap copies
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
   * Exhales SIL expression connectives (such as logical and/implication) and forwards the
   * translation of other expressions to the exhale components.
   */
  private def exhaleConnective(e: sil.Exp, error: PartialVerificationError, phase: Int): Stmt = {
    e match {
      case sil.And(e1, e2) =>
        exhaleConnective(e1, error, phase) ::
          exhaleConnective(e2, error, phase) ::
          Nil
      case sil.Implies(e1, e2) =>
        If(translateExp(e1), exhaleConnective(e2, error, phase), Statements.EmptyStmt)
      case sil.CondExp(c, e1, e2) =>
        If(translateExp(c), exhaleConnective(e1, error, phase), exhaleConnective(e2, error, phase))
      case _ if isInPhase(e, phase) =>
        components map (_.exhaleExp(e, error))
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
