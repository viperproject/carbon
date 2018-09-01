package viper.carbon.modules

import viper.silver.{ast => sil}
import viper.carbon.boogie._

/**
  * The comprehension module translates comprehension expressions.
  * Before translating a statement which includes a comprehension expression, the [[startNextStatement]] method should
  * be called first, then the statement should be translated, and afterwards the output of the [[filterPreamble]]
  * method should be handled (and outputed) first, before outputing the translated statement.
  * The reason for this is, that every filter needs to be axiomatized in the state in which it is used
  * (mentioned in a comprehension expression).
  */
trait ComprehensionModule extends Module {

  /**
    * An exception that indicates, when someone tried to translate a comprehension expression without
    * preparing the module for it with a [[startNextStatement]] call.
    */
  class UnexpectedCompExprException extends Exception

  /**
    * An exception indicating, that a new statement was tried to be started, without requesting the filter preamble
    * of the previous statement.
    */
  class UnexpectedStmtStartException extends Exception

  /**
    * Translate a comprehension expression.
    * @throws UnexpectedCompExprException if the translation was not prepared with a call to [[startNextStatement]]
    */
  @throws(classOf[UnexpectedCompExprException])
  def translateComp(e: sil.Exp): Exp

  /**
    * This method should be called, before a statement is translated, to start handling new occurring filters.
    * The comprehension module tracks filters that occurr newly,
    * that a respective preamble can be generated before the next statement to
    * axiomatize (initialize) the used filter in the statement.
    * @see [[filterPreamble]]
    * @throws UnexpectedStmtStartException if this method is called before requesting the filter preamble of the
    *                                      previously started statement, which means that the previous statement
    *                                      wasn't handled correctly.
    */
  @throws(classOf[UnexpectedStmtStartException])
  def startNextStatement()

  /**
    * Outputs a list of boolean-typed expressions, which serve as axiomatizations for the translated filters.
    * The module handling the current statement is responsible for inserting the axiomatizations (the returned list)
    * in an appropriate way, e.g. within an assume statement.
    * Since the comprehension module does not know, in which context a comprehension expression is translated,
    * the output of the filter preamble must be the responsibility of the module handling the current statement.
    *
    * Calling this method also disables the ability to translate a comprehension expression,
    * until the [[startNextStatement]] method is called again.
    *
    * @see [[startNextStatement]]
    */
  def filterPreamble(): Seq[Exp]

  /**
    * Outputs a list of identifiers, which are the identifiers for filters translated newly by this module for the
    * current statement.
    */
  def filterPreambleIdentifiers(): Seq[Identifier]

  /**
    * Returns whether it is currently allowed to translate comprehensions,
    * i.e. the [[startNextStatement]] method has been called after the previous call to [[filterPreamble]].
    *
    * @see [[startNextStatement]], [[filterPreamble]]
    */
  def canTranslateComprehension: Boolean
}
