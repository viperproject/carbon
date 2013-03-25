package semper.carbon.modules

import components.{InhaleComponent, ComponentRegistry}
import semper.sil.{ast => sil}
import semper.carbon.boogie.{Stmt, Exp}

/**
 * A module for translating inhale statements.  The module takes care of the basic
 * structure of inhaling as well as inhaling boolean connectives
 * such as logical and or logical implication.  Other modules can register themselves
 * as [[semper.carbon.modules.components.InhaleComponent]]s to perform the inhale
 * operation of certain expressions.
 *
 * The module also implements [[semper.carbon.modules.components.InhaleComponent]]
 * and performs some default behavior for most expressions.
 *
 * @author Stefan Heule
 */
trait InhaleModule extends Module with InhaleComponent with ComponentRegistry[InhaleComponent] {
  def inhale(exp: Seq[sil.Exp]): Stmt
}
