// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.carbon

import viper.silver.reporter.StdIOReporter
import viper.silver.testing.BackendTypeTest
import viper.silver.verifier.Verifier

class CarbonBackendTypeTest extends BackendTypeTest {
  override val verifier: Verifier = CarbonVerifier(StdIOReporter())
}
