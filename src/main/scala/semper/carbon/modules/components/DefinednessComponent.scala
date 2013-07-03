package semper.carbon.modules.components

import semper.carbon.boogie.{Statements, Stmt}
import semper.sil.{ast => sil}
import semper.sil.verifier.PartialVerificationError

/**
 * Takes care of determining whether expressions are well-formed.
 *
 * @author Stefan Heule
 */
trait DefinednessComponent extends Component {

  /**
   * Free assumptions about an expression.
   */
  def freeAssumptions(e: sil.Exp): Stmt = Statements.EmptyStmt

  /**
   * Proof obligations for a given expression.
   */
  def simplePartialCheckDefinedness(e: sil.Exp, error: PartialVerificationError): Stmt = Statements.EmptyStmt

  /**
   * Proof obligations for a given expression.  The first part of the result is used before
   * visiting all subexpressions, then all subexpressions are checked for definedness, and finally
   * the second part of the result is used.
   */
  def partialCheckDefinedness(e: sil.Exp, error: PartialVerificationError): (() => Stmt, () => Stmt) =
    (() => simplePartialCheckDefinedness(e, error), () => Statements.EmptyStmt)
}
