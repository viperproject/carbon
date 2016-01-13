package viper.carbon.modules.components

/**
 * Created by Gaurav on 08.03.2015.
 */

import viper.carbon.boogie.{LocalVar, Exp, Stmt}
import viper.silver.ast.LocationAccess
import viper.silver.{ast => sil}
import viper.carbon.modules.{TransferableEntity, StateModule}

/**
 *used to handle the transfer operation across different modules
 */
trait TransferComponent extends Component {
  /**
   *
   * @param e
   * @return the statements
   */
  def transferValid(e: TransferableEntity):Seq[(Stmt,Exp)]

  /**
   *
   * @param e
   * @param cond all assumptions and assertions should be wrapped inside an if statement with condition cond
   * @return  statement which adds the expression e to the current state (for example permissions, wand)
   */
  def transferAdd(e:TransferableEntity, cond: Exp): Stmt

  /**
   *
   * @param e
   * @param cond all assumptions and assertions should be wrapped inside an if statement with condition cond
   * @return  statement which removes the expression e to the current state (for example permissions, wand)
   */
  def transferRemove(e:TransferableEntity, cond:Exp): Stmt
}
