// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules

import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.modules.components.CarbonStateComponent
import viper.silver.ast.{LocationAccess, MagicWand}

/**
 * A module for translating heap expressions (access, updating) and determining
 * the heap encoding.
 */
trait HeapModule extends Module with CarbonStateComponent {

  /**
    * The type used for heaps
    */
  def heapType: Type

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
   * Get a function application representing that one heap-state (as represented by currentStateContributions of HeapModule) is a predecessor of another
   */
  def successorHeapState(first: Seq[LocalVarDecl], second: Seq[LocalVarDecl]) : Exp

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
   * Translation of a resource access (field read/write, predicate or wand instance)
   */
  def translateResourceAccess(r: sil.ResourceAccess): Exp = r match {
    case la: LocationAccess => translateLocationAccess(la)
    case mw: MagicWand => sys.error(s"Unexpectedly found magic wand $mw")
  }

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

  /**
    * Adds assumption that current heap equals heap represented by s
    */
  def equateWithCurrentHeap(s: Seq[Var]): Stmt

  // returns wand#sm (secondary mask for the wand)
  def wandMaskIdentifier(f: Identifier): Identifier

  // returns wand#ft (footprint of the magic wand)
  // this is inhaled at the beginning of packaging a wand to frame fields while the wand being packaged (
  // as the permission to the wand is gained at the end of the package statement)
  def wandFtIdentifier(f: Identifier): Identifier

  def predicateMaskFieldTypeOfWand(wand: String): Type

  def predicateVersionFieldTypeOfWand(wand: String): Type

  // adds permission to field e to the secondary mask of the wand
  def addPermissionToWMask(wMask: Exp, e: sil.Exp): Stmt

  // If expression evaluates to true then resultHeap is the sum of of heap1, where mask1 is defined,
  // and heap2, where mask2 is defined.
  def sumHeap(resultHeap: Exp, heap1: Exp, mask1: Exp, heap2: Exp, mask2: Exp): Exp
}
