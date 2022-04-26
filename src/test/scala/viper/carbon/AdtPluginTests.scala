// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon

import viper.silver.frontend.Frontend
import viper.silver.logger.SilentLogger
import viper.silver.reporter.{NoopReporter, StdIOReporter}
import viper.silver.testing.SilSuite
import viper.silver.verifier.Verifier

import java.nio.file.Path

/** All tests for the Adt Plugin. */
class AdtPluginTests extends SilSuite {
   override def testDirectories: Seq[String] = Vector("adt")

  override def frontend(verifier: Verifier, files: Seq[Path]): Frontend = {
    require(files.length == 1, "tests should consist of exactly one file")
    val fe = new CarbonFrontend(NoopReporter, SilentLogger().get)
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  val carbon: CarbonVerifier = CarbonVerifier(StdIOReporter())

  lazy val verifiers = List(carbon)

  override def configureVerifiersFromConfigMap(configMap: Map[String, Any]): Unit = {
    carbon.parseCommandLine(Seq("--plugin", "viper.silver.plugin.standard.adt.AdtPlugin") :+ "dummy-file-to-prevent-cli-parser-from-complaining-about-missing-file-name.silver.vpr")
  }


}
