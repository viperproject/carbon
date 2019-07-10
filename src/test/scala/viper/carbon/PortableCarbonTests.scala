// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.carbon

import java.nio.file.Path

import org.scalatest.DoNotDiscover
import viper.silver.frontend.Frontend
import viper.silver.logger.SilentLogger
import viper.silver.reporter.NoopReporter
import viper.silver.testing.{SilSuite, StatisticalTestSuite}
import viper.silver.verifier.Verifier


/**
  * Currently, we do not run the graph tests by default. This could be easily changed later by removing the
  * [[DoNotDiscover]] annotation.
  */
@DoNotDiscover
class PortableCarbonTests extends SilSuite with StatisticalTestSuite {

  override def verifier = CarbonVerifier()

  override def frontend(verifier: Verifier, files: Seq[Path]): Frontend = {
    require(files.length == 1, "tests should consist of exactly one file")
    val fe = new CarbonFrontend(NoopReporter, SilentLogger().get)
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }

  override val numOfExecutions: Int = Option(System.getenv("GRAPHS_REPETITIONS")) match {
    case Some(reps) =>
      val intReps = reps.toInt
      require(intReps >= 1)
      intReps
    case None => 1
  }
}
