/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.modules.components.CarbonStateComponent

/**
 * A module for translating heap expressions (access, updating) and determining
 * the heap encoding.
 */
trait HeapModule extends Module with CarbonStateComponent {

  /**
   * The type used for references.
   */
  def refType: Type

  /**
   * The type used for fields.
   */
  def fieldType: Type

  /**
   * The type used for fields of type t.
   */
  def fieldTypeOf(t: Type): Type

  /**
   * The type used for predicates.
   */
  def predicateVersionFieldType(genericT: String = "A"): Type

  /**
   * The type used for predicates mask fields.
   */
  def predicateMaskFieldType: Type

  /**
   * The type used for predicates mask fields of a given predicate family.
   */
  def predicateMaskFieldTypeOf(p: sil.Predicate): Type

  /**
   * The type used for predicates of a given family.
   */
  def predicateVersionFieldTypeOf(p: sil.Predicate): Type

  /**
   *
   */

  /**
   * The type used for wands.
   */
  def wandFieldType(wandName: String): Type

  /**
   * new type introduced for a wand
   */
  def wandBasicType(wandName: String):Type

  /**
   * Definitions for a field.
   */
  def translateField(f: sil.Field): Seq[Decl]

  /**
   * Definitions for the ghost field of a predicate.
   */
  def predicateGhostFieldDecl(f: sil.Predicate): Seq[Decl]

  /**
   * Translation of a field read or predicate instance
   */
  def translateLocationAccess(f: sil.LocationAccess): Exp
  /**
    * Translation of a field read.
    */
  def translateLocationAccess(rcv: Exp, loc:Exp):Exp

  def translateLocation(f: sil.LocationAccess): Exp
  def translateLocation(pred: sil.Predicate, args: Seq[Exp]): Exp

  /**
   * Translation of the null literal.
   */
  def translateNull: Exp

  /**
   * Check that the receiver of a location access is non-null.
   */
  def checkNonNullReceiver(loc: sil.LocationAccess): Exp = {
    loc match {
      case sil.FieldAccess(rcv, _) =>
        verifier.expModule.translateExp(rcv) !== translateNull
      case _ => TrueLit()
    }
  }

  def checkNonNullReceiver(rcv: Exp):Exp = {
    rcv !== translateNull
  }

  /**
   * Begin of exhale.
   */
  def beginExhale: Stmt

  /**
   * End of exhale
   */
  def endExhale: Stmt

  /**
   * Is the given field a predicate field?
   */
  def isPredicateField(f: Exp): Exp

  /**
    * get Predicate Id (unique for each Predicate)
    */
  def getPredicateId(f:Exp): Exp

  /**
    * Predicate name mapping to Id
    */

  def getPredicateId(s:String):BigInt
  /**
   * Is the given field a wand field?
   */
  def isWandField(f: Exp): Exp

  def predicateTrigger(extras: Seq[Exp], pred: sil.PredicateAccess, anyState: Boolean = false): Exp

  def currentHeap:Seq[Exp]

  def identicalOnKnownLocations(heap:Seq[Exp],mask:Seq[Exp]):Exp
}
