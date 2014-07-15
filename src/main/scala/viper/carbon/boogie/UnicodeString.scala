/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.boogie

import language.implicitConversions

/**
 * A class to extend strings with an `or` method that allows one
 * to use a Unicode string with a backup option if the file encoding used
 * is not UTF-8.

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
