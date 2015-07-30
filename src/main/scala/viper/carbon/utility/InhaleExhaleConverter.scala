package viper.carbon.utility

import viper.silver.ast.{InhaleExhaleExp, Exp}

/**
 * A helper object for converting InhaleExhale expressions to their
 * inhale or exhale parts.
 */
object InhaleExhaleConverter {

  def toInhale(exp: Exp): Exp = {
    exp.transform({
      case InhaleExhaleExp(in, ex) =>
        in
    })((_) => true)
  }

  def toExhale(exp: Exp): Exp = {
    exp.transform({
      case InhaleExhaleExp(in, ex) =>
        ex
    })((_) => true)
  }

}
