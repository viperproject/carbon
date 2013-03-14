package semper.carbon.modules

import components.{ExhaleComponent, ComponentRegistry}
import semper.sil.{ast => sil}
import semper.carbon.boogie.{Stmt, Exp}

/**
 * A module for translating exhale statements.  The module takes care of the basic
 * structure of exhaling (like multiple phases) and exhaling boolean connectives
 * such as logical and or logical implication.  Other modules can register themselves
 * as [[semper.carbon.modules.components.ExhaleComponent]]s to perform the exhale
 * operation of certain expressions.
 *
 * The module also implements [[semper.carbon.modules.components.ExhaleComponent]]
 * and performs some default behavior for most expressions.
 *
 * @author Stefan Heule
 */
trait ExhaleModule extends Module with ExhaleComponent with ComponentRegistry[ExhaleComponent] {
  def exhale(exp: Seq[sil.Exp]): Stmt
}
