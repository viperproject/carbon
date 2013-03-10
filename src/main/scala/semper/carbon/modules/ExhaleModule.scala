package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie.{Stmt, Exp}

/**
 * A module for translating exhale statements.
 *
 * @author Stefan Heule
 */
trait ExhaleModule extends Module {
  def exhale(exp: sil.Exp): Stmt
}
