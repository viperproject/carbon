package semper.carbon.modules

import semper.carbon.boogie._
import semper.sil.{ast => sil}

/**
 * The permission module determines the encoding of permissions and allows to add or remove
 * permission.
 *
 * @author Stefan Heule
 */
trait PermModule extends Module {

  /**
   * The type used to represent permissions.
   */
  def permType: Type

  /**
   * Translate a permission amount
   */
  def translatePerm(e: sil.Exp): Exp

  /**
   * Translate a permission comparison
   */
  def translatePermComparison(e: sil.Exp): Exp

  /**
   * The number of phases during exhale.
   */
  def numberOfPhases: Int

  /**
   * The ID of the phase that this expression should be exhaled in.
   */
  def phaseOf(e: sil.Exp): Int

  /**
   * A short description of a given phase.
   */
  def phaseDescription(phase: Int): String

  /**
   * The current mask.
   */
  def currentMask: Seq[Exp]

  /**
   * A static reference to the mask.
   */
  def staticMask: Seq[LocalVarDecl]

  /**
   * Is the permission for a given expression positive (using the static mask).
   */
  def staticPermissionPositive(rcv: Exp, loc: Exp): Exp
}
