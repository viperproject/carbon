package viper.carbon.modules

import viper.silver.{ast => sil}

trait LoopModule extends Module {

  /* Returns method annotated with loop information and initializes loop module accordingly.
   * This must be called before starting the method translation and the returned method should be used for the
   * translation.
   */
  def initializeMethod(m: sil.Method): sil.Method

  // Return true iff the statement is solely used for the loop module itself and is irrelevant otherwise.
  def isLoopDummyStmt(s: sil.Stmt) : Boolean

  // Return true iff the axioms to sum states is required.
  def sumOfStatesAxiomRequired : Boolean
}
