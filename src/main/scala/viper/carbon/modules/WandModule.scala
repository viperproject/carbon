package viper.carbon.modules

/**
 * Created by Gaurav on 06.03.2015.
 */

import viper.carbon.modules.components.{TransferComponent, ComponentRegistry}
import viper.silver.{ast => sil}
import viper.carbon.boogie.{Stmt}


trait WandModule extends Module with ComponentRegistry[TransferComponent] {
  def translatePackage(p: sil.Package):Stmt

//  def translateApply(p: sil.Apply):Stmt

}
