// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules

import components.{ComponentRegistry, DefinednessState, ExhaleComponent}
import viper.silver.{ast => sil}
import viper.carbon.boogie.Stmt
import viper.silver.verifier.PartialVerificationError

/**
 * A module for translating exhale statements.  The module takes care of the basic
 * structure of exhaling (like multiple phases) and exhaling boolean connectives
 * such as logical and or logical implication.  Other modules can register themselves
 * as [[viper.carbon.modules.components.ExhaleComponent]]s to perform the exhale
 * operation of certain expressions.
 *
 * The module also implements [[viper.carbon.modules.components.ExhaleComponent]]
 * and performs some default behavior for most expressions.

 */
trait ExhaleModule extends Module with ExhaleComponent with ComponentRegistry[ExhaleComponent] {

  /**
    * @param exp         A sequence of triples where the conjunction of the corresponding expressions (projection on the
    *                    the first element) is to be exhaled. The triple includes the error to be raised if the exhale fails and
    *                    the error to be raised if a well-definedness check fails during the exhale (if the latter is set
    *                    to [[None]], then no well-definedness checks are performed).
    * @param havocHeap   A boolean used to allow or prevent havocing the heap after the exhale.
    *                    For example, the heap is not havoced after the exhale when translating a fold statement.
    * @param isAssert    A boolean that tells whether the exhale method is being called during an exhale statement or an assert statement
    *                    (Assert reuses the code for exhale).
    *                    This is used for optimization purposes (remove extra operations if the statement is an 'assert')
    *                    and also used to translate the 'assert' statements during packaging a wand.
    * @param statesStackForPackageStmt stack of states used to translate statements during packaging a wand (carries currentState and LHS of wands)
    * @param insidePackageStmt      Boolean that represents whether this method is being called during packaging a wand or not.
    *
    * The 'statesStackForPackageStmt' and 'insidePackageStmt' are used when translating statements during packaging a wand.
    * For more details refer to the note in the wand module.
    */
  def exhale(exp: Seq[(sil.Exp, PartialVerificationError, Option[PartialVerificationError])], havocHeap: Boolean = true,
             isAssert: Boolean = false, statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false): Stmt

  /** convenience methods */

  def exhaleWithoutDefinedness(exp: Seq[(sil.Exp, PartialVerificationError)], havocHeap: Boolean = true,
                               isAssert: Boolean = false, statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false): Stmt = {
    exhale(exp.map(eError => (eError._1, eError._2, None)), havocHeap = havocHeap, isAssert = isAssert, statesStackForPackageStmt, insidePackageStmt = insidePackageStmt)
  }

  def exhaleSingleWithoutDefinedness(exp: sil.Exp, exhaleError: PartialVerificationError, havocHeap: Boolean = true,
                                     isAssert: Boolean = false, statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false): Stmt = {
    exhale(Seq((exp, exhaleError, None)), havocHeap = havocHeap, isAssert = isAssert, statesStackForPackageStmt, insidePackageStmt = insidePackageStmt)
  }

  def exhaleSingleWithDefinedness(exp: sil.Exp, exhaleError: PartialVerificationError, definednessError: PartialVerificationError,
                                  havocHeap: Boolean = true, isAssert: Boolean = false, statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false) = {
    exhale(Seq((exp, exhaleError, Some(definednessError))), havocHeap = havocHeap, isAssert = isAssert,
      statesStackForPackageStmt, insidePackageStmt = insidePackageStmt)
  }

}