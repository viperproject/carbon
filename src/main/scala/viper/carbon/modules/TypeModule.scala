/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie.Type

/**
 * A module for translating types.

 */
trait TypeModule extends Module {
  def translateType(typ: sil.Type): Type
}
