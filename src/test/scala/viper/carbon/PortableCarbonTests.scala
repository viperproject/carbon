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


/** This test mechanism is intended for running non-default test suites,
 * in a portable way. Example run command:
 *
 * ```
 * Z3_EXE=z3.exe
 * BOOGIE_EXE=Boogie.exe
 * sbt "test:runMain
 *      -DCARBONTESTS_TARGET=./target
 *      -DCARBONTESTS_WARMUP=./warmup
 *      -DCARBONTESTS_REPETITIONS=5
 *      -DCARBONTESTS_CSV=data.csv
 *      org.scalatest.tools.Runner
 *      -o -s
 *      viper.carbon.PortableCarbonTests"
 * ```
 *
 * The command above will:
 * 1. Warm-up the JVM by verifying all .vpr files in ./warmup
 * 2. Measure time of 5 runs of each .vpr file in ./target
 * 3. Discard ("trim") the slowest and the fastest runs and compute
 *   - the mean
 *   - absolute and relative standard deviation
 *   - the best
 *   - the median
 *   - the worst
 *   run times of all these tests, and
 * 4. Print the timing info (per phase) into STDOUT, and write mean and standard deviation
 *    to file data.csv
 * 5. Create JAR files (e.g., target/scala-2.12/silicon_2.12-1.1-SNAPSHOT.jar,
 *                            target/scala-2.12/silicon_2.12-1.1-SNAPSHOT-tests.jar)
 *    that can be used to run tests with SBT without the need to distribute/ recompile
 *    the Viper sources. To run the test without recompiling the sources, these
 *    JAR files should be put into a directory test-location/lib/
 *    where test-location/ is the directory where you invoke SBT via:
 *    ```
 *    sbt "set trapExit := false" \
 *    "test:runMain org.scalatest.tools.Runner -o -s viper.silicon.tests.PortableCarbonTests"
 *    ```
 *    Note that this command takes the same JVM property arguments as used above.
 *
 * The warmup and the target must be disjoint (not in a sub-directory relation).
 *
 * The following JVM properties are available:
 *   - CARBONTESTS_TARGET = path/to/target/files/    // Mandatory
 *   - CARBONTESTS_WARMUP = path/to/warmup/files/    // Optional. If not specified, skip JVM warmup phase.
 *   - CARBONTESTS_REPETITIONS = n // Optional, defaults to 1. If less then 3, no "trimming" will happen.
 *   - CARBONTESTS_CSV = path/to/file.csv // Optional. If provided, mean & stddev are written to CSV file.
 */
@DoNotDiscover
class PortableCarbonTests extends SilSuite with StatisticalTestSuite {
  /** Following a hyphenation-based naming scheme is important for handling project-specific annotations.
   * See comment for [[viper.silver.testing.TestAnnotations.projectNameMatches()]].
   */
  override def name = "Carbon-Statistics"

  override val repetitionsPropertyName = "CARBONTESTS_REPETITIONS"
  override val warmupLocationPropertyName = "CARBONTESTS_WARMUP"
  override val targetLocationPropertyName = "CARBONTESTS_TARGET"
  override val csvFilePropertyName = "CARBONTESTS_CSV"

  override def verifier: CarbonVerifier = CarbonVerifier()

  override def frontend(verifier: Verifier, files: Seq[Path]): Frontend = {
    require(files.length == 1, "tests should consist of exactly one file")
    val fe = new CarbonFrontend(NoopReporter, SilentLogger().get)
    fe.init(verifier)
    fe.reset(files.head)
    fe
  }
}
