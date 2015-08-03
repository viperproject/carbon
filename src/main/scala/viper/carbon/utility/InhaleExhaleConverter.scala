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

  def containsInhaleExhale(exp: Exp): Boolean = {
    exp.find {
      case e: InhaleExhaleExp => true
      case _ => false
    } match {
      case Some(node) => true
      case None => false
    }
  }

  def containsInhaleExhale(exps: Seq[Exp]): Boolean = {
    exps.exists(containsInhaleExhale(_))
  }

}
