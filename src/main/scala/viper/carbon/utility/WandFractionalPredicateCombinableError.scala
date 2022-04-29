package viper.carbon.utility

import viper.silver.ast.Program
import viper.silver.verifier.{AbstractVerificationError, ErrorReason, errors}

case class WandFractionalPredicateCombinableError(offendingNode: Program, reason: ErrorReason, override val cached: Boolean = false) extends AbstractVerificationError {
  val id = "wand.maybe.not.combinable"
  val text = s"Packaged magic wands might not be combinable."

  def withNode(offendingNode: errors.ErrorNode = this.offendingNode) = WandFractionalPredicateCombinableError(offendingNode.asInstanceOf[Program], this.reason, this.cached)
  def withReason(r: ErrorReason) = WandFractionalPredicateCombinableError(offendingNode, r, cached)
}
