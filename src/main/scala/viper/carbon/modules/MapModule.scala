// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules

import viper.silver.{ast => sil}
import viper.carbon.boogie.{Type, Exp}

/**
  * A module for translating maps.
  */
trait MapModule extends Module {
  def isUsed() : Boolean
  def translateMapExp(exp : sil.Exp) : Exp
  def translateMapType(mapType : sil.MapType) : Type
}
