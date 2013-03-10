package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie.{Stmt, Exp}

/**
 * A module for translating inhale statements.
 *
 * @author Stefan Heule
 */
trait InhaleModule extends Module {
  def inhale(exp: sil.Exp): Stmt
}
