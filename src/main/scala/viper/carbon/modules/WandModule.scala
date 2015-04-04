package viper.carbon.modules

/**
 * Created by Gaurav on 06.03.2015.
 */

import viper.carbon.modules.components.{TransferComponent, ComponentRegistry}
import viper.silver.verifier.PartialVerificationError
import viper.silver.{ast => sil}
import viper.carbon.boogie.{Exp, Stmt}


trait WandModule extends Module with TransferComponent with ComponentRegistry[TransferComponent] {
  def translatePackage(p: sil.Package, error: PartialVerificationError):Stmt

  def transferValid(e:sil.Exp):Seq[(Stmt,Exp)]

  def transferAdd(e:sil.Exp, cond: Exp): Stmt

  def transferRemove(e:sil.Exp, cond:Exp): Stmt

  //  def translateApply(p: sil.Apply):Stmt

}
