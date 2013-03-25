package semper.carbon.modules.components

import semper.carbon.boogie.Stmt
import semper.sil.{ast => sil}
import semper.sil.verifier.PartialVerificationError

/**
 * Takes care of inhaling one or several kinds of expressions.
 *
 * @author Stefan Heule
 */
trait InhaleComponent extends Component {

  /**
   * Exhale a single expression.
   */
  def inhaleExp(exp: sil.Exp): Stmt
}
