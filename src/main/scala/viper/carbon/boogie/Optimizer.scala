/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.boogie

/**
 * Optimize a given Boogie program or expression.

 */
object Optimizer {

  /**
   * Optimizes a Boogie program or expression by performing the following simplifications:
   * - Constant folding for booleans, integers and reals.
   * - Removal of dead branches.
   * - Removal of assertions known to hold.
   *
   * Constant folding partly taken from  Transformer.simplify from SIL, but added more optimizations.
   */
  def optimize(n: Node): Node = {
    /* Always optimize children first, then treat parent. */
    Transformer.transform(n)(_ => true, {
      case UnExp(Not, BoolLit(literal)) =>
        BoolLit(!literal)
      case UnExp(Not, UnExp(Not, single)) => single

      case BinExp(TrueLit(), And, right) => right
      case BinExp(left, And, TrueLit()) => left
      case BinExp(FalseLit(), And, _) => FalseLit()
      case BinExp(_, And, FalseLit()) => FalseLit()

      case BinExp(FalseLit(), Or, right) => right
      case BinExp(left, Or, FalseLit()) => left
      case BinExp(TrueLit(), Or, _) => TrueLit()
      case BinExp(_, Or, TrueLit()) => TrueLit()

      case BinExp(FalseLit(), Implies, _) => TrueLit()
      case BinExp(_, Implies, TrueLit()) => TrueLit()
      case BinExp(TrueLit(), Implies, FalseLit()) => FalseLit()
      case BinExp(TrueLit(), Implies, consequent) => consequent

      case BinExp(BoolLit(left), EqCmp, BoolLit(right)) => BoolLit(left == right)
      case BinExp(FalseLit(), EqCmp, right) => UnExp(Not, right)
      case BinExp(left, EqCmp, FalseLit()) => UnExp(Not, left)
      case BinExp(TrueLit(), EqCmp, right) => right
      case BinExp(left, EqCmp, TrueLit()) => left
      case BinExp(IntLit(left), EqCmp, IntLit(right)) => BoolLit(left == right)
      case BinExp(RealLit(left), EqCmp, RealLit(right)) => BoolLit(left == right)

      case BinExp(BoolLit(left), NeCmp, BoolLit(right)) => BoolLit(left != right)
      case BinExp(FalseLit(), NeCmp, right) => right
      case BinExp(left, NeCmp, FalseLit()) => left
      case BinExp(TrueLit(), NeCmp, right) => UnExp(Not, right)
      case BinExp(left, NeCmp, TrueLit()) => UnExp(Not, left)
      case BinExp(IntLit(left), NeCmp, IntLit(right)) => BoolLit(left != right)
      case BinExp(RealLit(left), NeCmp, RealLit(right)) => BoolLit(left != right)

      case CondExp(TrueLit(), ifTrue, _) => ifTrue
      case CondExp(FalseLit(), _, ifFalse) => ifFalse
      case CondExp(_, FalseLit(), FalseLit()) =>
        FalseLit()
      case CondExp(_, TrueLit(), TrueLit()) =>
        TrueLit()
      case CondExp(condition, FalseLit(), TrueLit()) =>
        UnExp(Not, condition)
      case CondExp(condition, TrueLit(), FalseLit()) => condition
      case CondExp(condition, FalseLit(), ifFalse) =>
        BinExp(UnExp(Not, condition), And, ifFalse)
      case CondExp(condition, TrueLit(), ifFalse) =>
        BinExp(condition, Or, ifFalse)
      case CondExp(condition, ifTrue, FalseLit()) =>
        BinExp(condition, And, ifTrue)
      case CondExp(condition, ifTrue, TrueLit()) =>
        BinExp(UnExp(Not, condition), Or, ifTrue)

      case Forall(_, _, BoolLit(literal), _) =>
        BoolLit(literal)
      case Exists(_, BoolLit(literal)) =>
        BoolLit(literal)

      case UnExp(Minus, IntLit(literal)) => IntLit(-literal)
      case UnExp(Minus, RealLit(literal)) => RealLit(-literal)
      case UnExp(Minus, UnExp(Minus, single)) => single

      case BinExp(IntLit(left), GeCmp, IntLit(right)) =>
        BoolLit(left >= right)
      case BinExp(IntLit(left), GtCmp, IntLit(right)) =>
        BoolLit(left > right)
      case BinExp(IntLit(left), LeCmp, IntLit(right)) =>
        BoolLit(left <= right)
      case BinExp(IntLit(left), LtCmp, IntLit(right)) =>
        BoolLit(left < right)

      case BinExp(IntLit(left), Add, IntLit(right)) =>
        IntLit(left + right)
      case BinExp(IntLit(left), Sub, IntLit(right)) =>
        IntLit(left - right)
      case BinExp(IntLit(left), Mul, IntLit(right)) =>
        IntLit(left * right)
     // This case was removed - the evaluation as doubles and translation of RealLit can introduce rounding/precision errors
     /* case BinExp(IntLit(left), Div, IntLit(right)) if right != 0 =>
        RealLit(left.toDouble / right.toDouble)*/
      case BinExp(IntLit(left), IntDiv, IntLit(right)) if right != 0 =>
        IntLit(left / right)
      case BinExp(IntLit(left), Mod, IntLit(right)) if right != 0 =>
        IntLit(left % right)

      case BinExp(RealLit(left), GeCmp, RealLit(right)) =>
        BoolLit(left >= right)
      case BinExp(RealLit(left), GtCmp, RealLit(right)) =>
        BoolLit(left > right)
      case BinExp(RealLit(left), LeCmp, RealLit(right)) =>
        BoolLit(left <= right)
      case BinExp(RealLit(left), LtCmp, RealLit(right)) =>
        BoolLit(left < right)

      case BinExp(RealLit(left), Add, RealLit(right)) =>
        RealLit(left + right)
      case BinExp(RealLit(left), Sub, RealLit(right)) =>
        RealLit(left - right)
      case BinExp(RealLit(left), Mul, RealLit(right)) =>
        RealLit(left * right)
      case BinExp(RealLit(left), Div, RealLit(right)) if right != 0 =>
        RealLit(left / right)
      case BinExp(RealLit(left), Mod, RealLit(right)) if right != 0 =>
        RealLit(left % right)

      case If(TrueLit(), thn, els) => thn
      case If(FalseLit(), thn, els) => els

      case If(c, thn, els) if thn.children.isEmpty && els.children.isEmpty =>
        Statements.EmptyStmt

      case Assert(TrueLit(), _) => Statements.EmptyStmt
      case Assume(TrueLit()) => Statements.EmptyStmt
    })
  }
}
