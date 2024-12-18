// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules

import viper.carbon.boogie._
import viper.carbon.modules.components.CarbonStateComponent
import viper.silver.{ast => sil}

case class PMaskDesugaredRep(selectId: Identifier, storeId: Identifier)

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
    * Returns an expression representing that a permission amount is positive.
    * Similar to [[permissionPositive]], but works directly on Viper expressions, *including* ones containing
    * wildcards, and performs more aggressive simplifications.
    *
    * @param e the permission amount to be checked
    * @return the expression representing the fact that the permission is positive
    */
  def isStrictlyPositivePerm(e: sil.Exp): Exp

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
    * The wand mask field of a given wand (as its ghost location).
    */
  def wandMaskField(wand: Exp): Exp

  /**
    * The type used for masks.
    */
  def maskType: Type

  /**
   * The type used to for predicate masks.
   */
  def pmaskType: Type

  /**
    * The desugared poly map version of [[pmaskType]].
    * TODO: It may make sense to move the representation of predicate masks to another module. Right now the representation
    *       seems to be shared among multiple modules.
    */
  def pmaskTypeDesugared: PMaskDesugaredRep

  def zeroPMask: Exp

  def hasDirectPerm(ra: sil.ResourceAccess): Exp

  /**
   * The expression for the current permission at a location.
   */
  def currentPermission(loc: sil.ResourceAccess): Exp

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

  /**
    *
    * @param summandMask1
    * @param summandMask2
    * @return expression for which its validity implies that the current mask is the sum of the two input masks
    */
  def sumMask(summandMask1: Seq[Exp], summandMask2: Seq[Exp]): Exp

  /**
    *
    * @param resultMask
    * @param summandMask1
    * @param summandMask2
    * @return expression for which its validity implies that @{code resultMask} is the sum of the other two input
    *         masks
    */
  def sumMask(resultMask: Seq[Exp], summandMask1: Seq[Exp], summandMask2: Seq[Exp]) : Exp

    /** returns a mask and the returned statement ensures that the mask  has non-zero permission at rcv.loc and zero
      * permission at all other location
      * this should only be used temporarily, i.e. if there are two calls to this then the previous tempMask returned
      * will be overwritten in the Boogie code
      */
  def tempInitMask(rcv: Exp, loc:Exp):(Seq[Exp], Stmt)

  def getCurrentAbstractReads(): collection.mutable.ListBuffer[String]

  /**
    * Checks if expression e contains instances of wildcards
    */

  def containsWildCard(e: sil.Exp): Boolean

  // adds permission to w#ft (footprint of the magic wand) (See Heap module for w#ft description)
  def inhaleWandFt(w: sil.MagicWand): Stmt

  // removes permission to w#ft (footprint of the magic wand) (See Heap module for w#ft description)
  def exhaleWandFt(w: sil.MagicWand): Stmt

  def setCheckReadPermissionOnly(readOnly: Boolean): Boolean

  def assumePermUpperBounds(doAssume: Boolean): Stmt

}
