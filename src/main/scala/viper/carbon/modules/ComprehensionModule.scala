package viper.carbon.modules

import viper.silver.{ast => sil}
import viper.carbon.boogie._

/**
  * The comprehension module translates comprehension expressions.
  */
trait ComprehensionModule extends Module {

  /**
    * Translate a comprehension expression.
    */
  def translateComp(e: sil.Exp): Exp
}
