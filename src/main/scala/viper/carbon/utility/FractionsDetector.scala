package viper.carbon.utility

import viper.silver.{ast => sil}

object FractionsDetector {
  private def permTypedExpPotentiallyHasFractions(e:sil.Exp) : Boolean = {
    e match {
      case _ : sil.FullPerm => false
      case _ : sil.NoPerm => false
      case sil.CondExp(_, thn, els) => permTypedExpPotentiallyHasFractions(thn) || permTypedExpPotentiallyHasFractions(els)
      case _ => true
    }
  }

  def potentiallyHasFractions(e: sil.Node): Boolean= {
    e.existsDefined(
      n => n match {
        case acc : sil.AccessPredicate if permTypedExpPotentiallyHasFractions(acc.perm) => true
      }
    )
  }

  def hasPredicatePermission(e: sil.Node): Boolean = {
    e.existsDefined(
      n => n match {
        case acc: sil.PredicateAccessPredicate => true
      }
    )
  }
}
