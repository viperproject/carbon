package viper.carbon.modules

import viper.carbon.boogie.{RealLit, Exp}
import viper.silver.{ast => sil}

/**
 * Created by Gaurav on 02.05.2015.
 */
sealed trait TransferableEntity {
  def rcv: Exp
  def loc: Exp
  def transferAmount: Exp
}

object TransferableEntity {
  def unapply(te: TransferableEntity) = Some((te.rcv,te.loc,te.transferAmount))
}

case class TransferableAccessPred(rcv: Exp, loc:Exp, transferAmount: Exp) extends TransferableEntity

case class TransferableWand(rcv:Exp, loc: Exp, transferAmount: Exp = RealLit(1.0)) extends TransferableEntity
