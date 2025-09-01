// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.carbon

import viper.silver.testing.{CounterexampleTestInput, DefaultAnnotatedTestInput}

import java.nio.file.Path


class GeneralCounterexampleTests extends AllTests {
  override val testDirectories: Seq[String] = Seq("counterexample_mapped", "counterexample_general")

  override val commandLineArguments: Seq[String] =
    Seq("--counterexample=extended")

  override def buildTestInput(file: Path, prefix: String): DefaultAnnotatedTestInput = {
    CounterexampleTestInput(file, prefix)
  }
}