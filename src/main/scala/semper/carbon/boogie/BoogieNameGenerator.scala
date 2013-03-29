package semper.carbon.boogie

import semper.sil.utility.NameGenerator

/**
 * 
 * @author Stefan Heule
 */
class BoogieNameGenerator extends NameGenerator {
  // in principle, some others would also be allowed, but this is good enough for now
  private val otherChars = "_.$#'`~^\\?a-zA-Z"
  def firstCharacter = s"[$otherChars]".r
  def otherCharacter = s"[0-9$otherChars]".r
  def separator = "_"
}
