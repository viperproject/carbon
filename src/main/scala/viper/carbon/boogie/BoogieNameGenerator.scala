/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.boogie

import viper.silver.utility.DefaultNameGenerator

class BoogieNameGenerator extends DefaultNameGenerator {
  // in principle, some others would also be allowed, but this is good enough for now
  private val otherChars = "_.$#'`~^\\?a-zA-Z"
  def firstCharacter = s"[$otherChars]".r
  def otherCharacter = s"[0-9$otherChars]".r
  def separator = "_"
  def reservedNames: Set[String] = Set("div", "const", "procedure", "type", "function", "uniqu", "complete", "if", "else", "free",
    "invariant", "goto", "break", "return", "call", "forall", "assert", "havoc", "assume", "returns", "var", "implementation",
    "axiom", "exists", "old", "false", "real", "int", "true", "bool", "finite", "ensures", "requires", "where") ++
    Set("Set", "MultiSet", "Seq")
}
