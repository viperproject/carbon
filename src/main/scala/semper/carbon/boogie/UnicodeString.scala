package semper.carbon.boogie

import language.implicitConversions

/**
 * A class to extend strings with an `or` method that allows one
 * to use a Unicode string with a backup option if the file encoding used
 * is not UTF-8.
 *
 * @author Stefan Heule
 */
class UnicodeString(val s: String) {
  def or(safe: String) = {
    //if (System.getProperty("file.encoding") == "UTF-8") s else safe
    safe
  }
}
object UnicodeString {
  implicit def string2unicodestring(s: String) = new UnicodeString(s)
}
