package semper.carbon.modules.components

import semper.sil.{ast => sil}
import semper.carbon.boogie.{Statements, Stmt}

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

  /**
   * This method is called at the beginning of translating a fresh read permission block,
   * and by default does nothing.
   */
  def enterFreshBlock(fb: sil.FreshReadPerm): Stmt = Statements.EmptyStmt

  /**
   * This method is called at the end of translating a fresh read permission block,
   * and by default does nothing.
   */
  def leaveFreshBlock(fb: sil.FreshReadPerm): Stmt = Statements.EmptyStmt
}
