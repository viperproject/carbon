package viper.carbon.modules

import viper.carbon.boogie.{RealLit, Exp}
import viper.silver.verifier.{PartialVerificationError, reasons, VerificationError}
import viper.silver.{ast => sil}

/**
 * Created by Gaurav on 02.05.2015.
 */
sealed trait TransferableEntity {
  def rcv: Exp
  def loc: Exp
  def transferAmount: Exp
  def originalSILExp: sil.Exp

  def transferError(error: PartialVerificationError):VerificationError
}

object TransferableEntity {
  def unapply(te: TransferableEntity) = Some((te.rcv,te.loc,te.transferAmount))
}

case class TransferableAccessPred(rcv: Exp, loc:Exp, transferAmount: Exp,originalSILExp: sil.AccessPredicate) extends TransferableEntity {
  override def transferError(error: PartialVerificationError):VerificationError = {
    error.dueTo(reasons.InsufficientPermission(originalSILExp.loc))
  }
}

case class TransferableWand(rcv:Exp, loc: Exp, transferAmount: Exp,originalSILExp: sil.MagicWand) extends TransferableEntity {
  override def transferError(error: PartialVerificationError): VerificationError = {
    error.dueTo(reasons.MagicWandChunkNotFound(originalSILExp))
  }
}
