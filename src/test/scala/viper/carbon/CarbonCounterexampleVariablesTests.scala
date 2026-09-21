// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.carbon

import viper.silver.reporter.StdIOReporter
import viper.silver.testing.{CounterexampleComparison, CounterexampleVariablesTests, ExpectedCounterexample, ExpectedValuesCounterexampleAnnotation, OutputAnnotationId, TestCustomError, TestError}
import viper.silver.verifier.{FailureContext, SimpleCounterexample}

import java.nio.file.Path

class CarbonCounterexampleVariablesTests extends AllTests with CounterexampleVariablesTests {
  override lazy val verifier: CarbonVerifier = {
    val carbon = CarbonVerifier(StdIOReporter())
    carbon.parseCommandLine(commandLineArguments ++ Seq("--counterexample=variables", "dummy.vpr"))
    carbon
  }

  override def createExpectedValuesCounterexampleAnnotation(id: OutputAnnotationId, file: Path, forLineNr: Int, expectedCounterexample: ExpectedCounterexample): ExpectedValuesCounterexampleAnnotation =
    CarbonExpectedValuesCounterexampleAnnotation(id, file, forLineNr, expectedCounterexample)
}

/** represents an expected output (identified by `id`) with an associated (possibly partial) counterexample model */
case class CarbonExpectedValuesCounterexampleAnnotation(id: OutputAnnotationId, file: Path, forLineNr: Int, expectedCounterexample: ExpectedCounterexample)
  extends ExpectedValuesCounterexampleAnnotation(id, file, forLineNr, expectedCounterexample) {

  def containsExpectedCounterexample(failureContext: FailureContext): Boolean =
    failureContext.counterExample match {
      case Some(silCounterexample: SimpleCounterexample) => CounterexampleComparison.meetsExpectations(expectedCounterexample, silCounterexample.model)
      case _ => false
    }

  override def notFoundError: TestError = TestCustomError(s"Expected the following counterexample on line $forLineNr: $expectedCounterexample")

  override def withForLineNr(line: Int = forLineNr): ExpectedValuesCounterexampleAnnotation = CarbonExpectedValuesCounterexampleAnnotation(id, file, line, expectedCounterexample)
}
