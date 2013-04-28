package semper.carbon.modules.components

import semper.carbon.boogie.Stmt
import semper.sil.{ast => sil}
import semper.sil.verifier.PartialVerificationError

/**
 * Takes care of determining whether expressions are well-formed.
 *
 * @author Stefan Heule
 */
trait DefinednessComponent extends Component {

  /**
   * Proof obligations for a given expression.
   */
  def partialCheckDefinedness(e: sil.Exp, error: PartialVerificationError): Stmt
}
