package viper.carbon.modules

import viper.silver.{ast => sil}

trait LoopModule extends Module {

  def initializeMethod(m: sil.Method): sil.Method

}
