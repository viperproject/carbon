package semper.carbon.modules

import semper.carbon.modules.components.{DefinednessComponent, StmtComponent, ComponentRegistry}
import semper.sil.{ast => sil}
import semper.carbon.boogie.Stmt

/**
 * A module for translating SIL statements.
 *
 * @author Stefan Heule
 */
trait StmtModule extends Module with ComponentRegistry[StmtComponent] {
  def translateStmt(stmt: sil.Stmt): Stmt
}
