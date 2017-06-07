/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules

import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.verifier.Environment

/**
 * A module for translating Viper programs by invoking the right modules and
 * gathering all the preambles, etc.
 */
trait MainModule extends Module {
  /**
   * Translate a Viper program into a Boogie program.
   */
  def translate(p: sil.Program): Program

  /**
   * Translate a local variable along with its type (into a boogie declaration).  Assumes that the variable is already
   * defined in the current environment.
   */
  def translateLocalVarSig(typ:sil.Type, v:sil.LocalVar): LocalVarDecl
  def translateLocalVarDecl(l: sil.LocalVarDecl): LocalVarDecl = {
    translateLocalVarSig(l.typ,l.localVar)
  }


  /** The current environment. */
  var env: Environment = null

  /** The namespace for Viper local variables. */
  def silVarNamespace: Namespace

  /** Used to encode assumptions made about valid values of a given type (e.g. allocation of non-null references) */
  /** the "isParameter" flag can be used to select assumptions which only apply to parameters */
  def allAssumptionsAboutValue(typ:sil.Type, arg: LocalVarDecl, isParameter: Boolean): Stmt
  def allAssumptionsAboutValue(arg:sil.LocalVarDecl, isParameter: Boolean) : Stmt = {
    allAssumptionsAboutValue(arg.typ,translateLocalVarDecl(arg),isParameter)
  }

}
