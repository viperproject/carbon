// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon

import org.scalatest.{Args, Status}
import viper.silver.testing.SilSuite
import viper.silver.verifier.Verifier
import viper.silver.frontend.Frontend

import java.nio.file.Path
import viper.silver.logger.SilentLogger
import viper.silver.reporter.{NoopReporter, StdIOReporter}

/** All tests for carbon.

  */
class AllTests extends SilSuite {
  override def testDirectories: Seq[String] = Vector(
    // "all/basic",
    // "all/chalice",
    // "all/domains",
    // "all/functions",
    // "all/heap-dependent_triggers",
    // "all/import",
    // "all/impure_assume",
    // "all/inhale_exhale",
    // "all/invariants",
    // "all/issues/carbon",
    // "all/issues/silicon",
    "all/issues/silver",
    // "all/macros",
    "wands/examples",
    // "quantifiedpermissions", "quantifiedpredicates",
    // "quantifiedcombinations", "examples", "termination", "refute"
  )

  override def frontend(verifier: Verifier, files: Seq[Path]): Frontend = {
    require(files.length == 1, "tests should consist of exactly one file")
    val fe = new CarbonFrontend(NoopReporter, SilentLogger().get)
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  lazy val verifiers = List(CarbonVerifier(StdIOReporter()))

  protected override def runTest(testName: String, args: Args): Status = {
    val modArgs = args.copy(configMap = args.configMap.updated("includeFiles", "(list_insert_tmp|02).*\\.vpr"))
    super.runTest(testName, modArgs)
  }
}
