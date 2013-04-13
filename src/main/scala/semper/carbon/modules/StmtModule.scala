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
  // because every trait can only extend ComponentRegistry, we have to duplicate some
  // logic here
  private var _definednessComponents: Seq[DefinednessComponent] = Nil
  def definednessComponents: Seq[DefinednessComponent] = _definednessComponents
  def registerDefinednessComponent(component: DefinednessComponent) {
    _definednessComponents = _definednessComponents :+ component
  }

  def translateStmt(stmt: sil.Stmt): Stmt
}
