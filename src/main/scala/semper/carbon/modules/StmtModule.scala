/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper.carbon.modules

import semper.carbon.modules.components.{DefinednessComponent, StmtComponent, ComponentRegistry}
import semper.sil.{ast => sil}
import semper.carbon.boogie.Stmt

/**
 * A module for translating SIL statements.

 */
trait StmtModule extends Module with ComponentRegistry[StmtComponent] {
  def translateStmt(stmt: sil.Stmt): Stmt
}
