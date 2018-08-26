package viper.carbon.modules

import viper.silver.{ast => sil}
import viper.carbon.boogie._

/**
  * The comprehension module determines the encoding of comprehension calls and determines what comprehensions need
  * to be created for all occurring calls.
  */
trait ComprehensionModule extends Module {

  /**
    * A class for describing a comprehension instance
    */
  case class Comprehension(name: String, vars: Seq[LocalVarDecl], body: Exp, binary: String, unit: Exp, typ: Type)

  /**
    * A class for describing a filter instance
    */
  class Filter(name: String, body: Exp)

  /**
    * All comprehensions occurring in the program
    */
  protected val comprehensions: Seq[Comprehension] = Seq()

  /**
    * All filters occurring in the program
    */
  protected val filters: Seq[Filter] = Seq()

  /**
    * Translate a comprehension expression
    */
  def translateComp(e: sil.Exp): Exp

  /**
    * Translate the body of a comprehension, i.e. the expression of the form e.v
    */
  def translateBody(e: sil.Exp): Exp

  /**
    * Translate the unit expression of a comprehension
    */
  def translateUnit(e: sil.Exp): Exp

  /**
    * Detects which comprehension of the currently available comprehensions (in [[comprehensions]]) is called by the
    * expression.
    *
    * @param c The call to a comprehension
    * @return The comprehension used in the call, wrapped inside Some, or None, if there is no instance of the called
    *         comprehension yet (a new instance has to be created).
    */
  def detectComp(c: sil.Comp): Option[Comprehension]

  /**
    * Detects which filter of the currently available filters (in [[filters]]) is used in the expression.
    *
    * @param f The filter expression to be checked against the available filter objects
    * @return The filter object used in the expression, wrapped inside Some, or None, if there is no such instance yet.
    */
  def detectFilter(f: sil.Filter): Option[Filter]

  /**
    * Translate a filter, i.e. register the filter in the [[filters]] sequence to generate its axiomatization in the
    * preamble and output the respective constant, which will be created in the preamble, as an expression to use in
    * the comprehension call.
    */
  def translateFilter(e: sil.Filter): Exp
}
