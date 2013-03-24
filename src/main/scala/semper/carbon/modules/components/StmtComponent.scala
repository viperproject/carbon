package semper.carbon.modules.components

import semper.sil.{ast => sil}
import semper.carbon.boogie.Stmt

/**
 * Contributes to the translation of one or several statements.
 *
 * @author Stefan Heule
 */
trait StmtComponent extends Component {

  /**
   * Potentially contributes to the translation of a statement.  If no contribution
   * is desired, then [[semper.carbon.boogie.Statements.EmptyStmt]] can be used as a
   * return value.
   */
  def handleStmt(s: sil.Stmt): Stmt
}
