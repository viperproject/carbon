/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import viper.carbon.boogie._
import viper.carbon.modules.components.{CarbonStateComponent}
import viper.silver.{ast => sil}

/**
 * The permission module determines the encoding of permissions and allows to add or remove
 * permission.

 */
trait PermModule extends Module with CarbonStateComponent {

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
   * Returns an expression representing that a permission amount is positive
   *
   * @param permission the permission amount to be checked
   * @param zeroOK whether the comparison should (not) be strict, or not
   * @return the expression representing the fact that the permission is positive
   */
  def permissionPositive(permission: Exp, zeroOK : Boolean = false): Exp


  def conservativeIsPositivePerm(e: sil.Exp): Boolean

  /**
   * The number of phases during exhale.
   */
  def numberOfPhases: Int

  /**
   * The ID of the phase that this expression should be exhaled in.
   */
  def isInPhase(e: sil.Exp, phaseId: Int): Boolean

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

  /**
   * The predicate mask field of a given predicate (as its ghost location).
   */
  def predicateMaskField(pred: Exp): Exp

  /**
   * The type used to for predicate masks.
   */
  def pmaskType: Type

  def zeroPMask: Exp

  def hasDirectPerm(la: sil.LocationAccess): Exp

  def permissionLookup(la: sil.LocationAccess) : Exp
/** FIXME: duplicate method, here */

  /**
   * The expression for the current permission at a location.
   */
  def currentPermission(loc: sil.LocationAccess): Exp

  def currentPermission(rcv:Exp, loc:Exp):Exp

  /**these methods are for experimental purposes, not yet finalized **/
  /*def beginSumMask : Stmt

  def sumMask : Exp

  def endSumMask: Stmt*/
/*
  def setSummandMask1
  def setSummandMask2
  def sumMask(assmsToSmt: Exp => Stmt):Stmt
  */

  def sumMask(summandMask1: Seq[Exp], summandMask2: Seq[Exp]): Exp

    /** returns a mask and the returned statement ensures that the mask  has non-zero permission at rcv.loc and zero
      * permission at all other location
      * this should only be used temporarily, i.e. if there are two calls to this then the previous tempMask returned
      * will be overwritten in the Boogie code
      */
  def tempInitMask(rcv: Exp, loc:Exp):(Seq[Exp], Stmt)

}
