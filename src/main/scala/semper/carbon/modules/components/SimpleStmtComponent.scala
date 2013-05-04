package semper.carbon.modules.components

import semper.sil.{ast => sil}
import semper.carbon.boogie.{Statements, Stmt}

/**
 * A statement component that only contributes at the end.
 *
 * @author Stefan Heule
 */
trait SimpleStmtComponent extends StmtComponent {

  /**
   * Potentially contributes to the translation of a statement.  If no contribution
   * is desired, then [[semper.carbon.boogie.Statements.EmptyStmt]] can be used as a
   * return value.
   */
  def simpleHandleStmt(s: sil.Stmt): Stmt

  override def handleStmt(s: sil.Stmt) = (Statements.EmptyStmt, simpleHandleStmt(s))
}
