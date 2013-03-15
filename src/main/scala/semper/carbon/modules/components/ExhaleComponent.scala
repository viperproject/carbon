package semper.carbon.modules.components

import semper.carbon.boogie.Stmt
import semper.sil.{ast => sil}
import semper.sil.verifier.PartialVerificationError

/**
 * Takes care of exhaling one or several kinds of expressions.
 *
 * @author Stefan Heule
 */
trait ExhaleComponent extends Component {

  /**
   * Exhale a single expression.
   */
  def exhaleExp(e: sil.Exp, error: PartialVerificationError): Stmt
}
