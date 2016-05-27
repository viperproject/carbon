/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.boogie

import language.implicitConversions

/**
 * A collection of implicits for working with the Boogie AST.

 */
object Implicits {
  implicit def lift[T](t: T): Seq[T] = Seq(t)
  implicit def liftStmt(ss: Seq[Stmt]) = Seqn(ss)
  implicit def liftSeq(ss: Seq[Exp]) = new BoolSeq(ss)

  /**
   * Adds methods to turn a sequence of expressions into their conjunction or disjunction.
   */
  class BoolSeq(xs: Seq[Exp]) {
    /** Returns the conjunction of all expressions, or 'true' if the sequence is empty'. */
    def all: Exp = all(xs).getOrElse(TrueLit())
    /** Returns the conjunction of all expressions, or 'None' if the sequence is empty'. */
    def allOption: Option[Exp] = all(xs)

    /** Returns the disjunction of all expressions, or 'false' if the sequence is empty'. */
    def any: Exp = any(xs).getOrElse(FalseLit())
    /** Returns the disjunction of all expressions, or 'None' if the sequence is empty'. */
    def anyOption: Option[Exp] = any(xs)

    private def any(xss: Seq[Exp]): Option[Exp] = {
      xss match {
        case Nil => None
        case Seq(x) => Some(x)
        case Seq(x, y) => Some(BinExp(x, Or, y))
        case x +: xs => Some(BinExp(x, Or, all(xs).get))
      }
    }

    private def all(xss: Seq[Exp]): Option[Exp] = {
      xss match {
        case Nil => None
        case Seq(x) => Some(x)
        case Seq(x, y) => Some(BinExp(x, And, y))
        case x +: xs => Some(BinExp(x, And, all(xs).get))
      }
    }
  }
}
