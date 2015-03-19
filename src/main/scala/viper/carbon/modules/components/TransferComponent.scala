package viper.carbon.modules.components

/**
 * Created by Gaurav on 08.03.2015.
 */

import viper.carbon.boogie.{LocalVar, Exp, Stmt}
import viper.silver.ast.LocationAccess
import viper.silver.{ast => sil}
import viper.carbon.modules.StateModule

/**
 *used to handle the transfer operation across different modules
 */
trait TransferComponent {
  /**
   *
   * @param e
   * @return (stmt,exp), After stmt is executed exp evaluates to true iff e can be transferred according to the specific component
   */
  def transferValid(e:sil.Exp):(Stmt,Exp)

  /**
   *
   * @param e
   * @param b all assumptions and assertions should be wrapped inside an if statement with condition b (b is a Boolean)
   * @return  statement which adds the expression e to the current state (for example permissions, wand)
   */
  def transferAdd(e:sil.Exp, b: LocalVar): Stmt

  /**
   *
   * @param e
   * @param b all assumptions and assertions should be wrapped inside an if statement with condition b (b is a Boolean)
   * @return  statement which removes the expression e to the current state (for example permissions, wand)
   */
  def transferRemove(e:sil.Exp, b:LocalVar): Stmt
}
