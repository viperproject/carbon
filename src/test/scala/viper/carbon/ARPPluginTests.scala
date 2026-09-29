// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.carbon

import viper.silver.frontend.Frontend
import viper.silver.logger.SilentLogger
import viper.silver.reporter.{NoopReporter, StdIOReporter}
import viper.silver.testing.SilSuite
import viper.silver.verifier.Verifier

import java.nio.file.Path

class ARPPluginTests extends AllTests {
  override val testDirectories: Seq[String] = Seq("arp")

  override val commandLineArguments: Seq[String] =
    Seq("--plugin", "viper.silver.plugin.standard.arp.ARPPlugin", "--timeout=180")
}
