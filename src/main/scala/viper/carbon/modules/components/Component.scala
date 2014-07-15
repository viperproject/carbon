/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.components

/**
 * Common trait for components.

 */
trait Component {
  /** The list of other components which need to come after this component. */
  var comesBefore: Seq[Any] = Nil
  /** The list of other components after which this component will be used. */
  var comesAfter: Seq[Any] = Nil
}
