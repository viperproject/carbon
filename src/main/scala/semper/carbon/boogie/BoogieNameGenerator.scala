package semper.carbon.boogie

import semper.sil.utility.DefaultNameGenerator

/**
 *
 * @author Stefan Heule
 */
class BoogieNameGenerator extends DefaultNameGenerator {
  // in principle, some others would also be allowed, but this is good enough for now
  private val otherChars = "_.$#'`~^\\?a-zA-Z"
  def firstCharacter = s"[$otherChars]".r
  def otherCharacter = s"[0-9$otherChars]".r
  def separator = "_"
  def reservedNames: Set[String] = Set("const", "procedure", "type", "function", "uniqu", "complete", "if", "else", "free",
    "invariant", "goto", "break", "return", "call", "forall", "assert", "havoc", "assume", "returns", "var", "implementation",
    "axiom", "exists", "old", "false", "real", "int", "true", "bool", "finite", "ensures", "requires", "where") ++
    Set("Set", "MultiSet", "Seq")
}
