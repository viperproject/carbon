// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

import scala.collection.mutable
import org.scalatest.funsuite.AnyFunSuite
import viper.carbon.CarbonVerifier
import viper.silver.reporter.{Message, QuantifierChosenTriggersMessage, Reporter}
import viper.silver.verifier.Success

/** Carbon infers triggers that respect Silver's `@noAutoTrigger()` annotation, also for a program that a client
  * builds as an AST and verifies directly, without parsing. */
class CarbonTriggerAnnotationTests extends AnyFunSuite {
  test("Carbon respects @noAutoTrigger() annotations in a program built as an AST") {
    val chosen = mutable.ArrayBuffer.empty[QuantifierChosenTriggersMessage]
    val reporter = new Reporter {
      val name = "CarbonTriggerAnnotationTests"
      def report(msg: Message): Unit = msg match {
        case m: QuantifierChosenTriggersMessage => chosen += m
        case _ =>
      }
    }
    val carbon = CarbonVerifier(reporter)
    carbon.parseCommandLine(Seq("dummy.vpr"))
    carbon.start()
    val result = try carbon.verify(AstBuiltTriggerProgram.encoded) finally carbon.stop()

    assert(result == Success)
    /* Inferred (not given) triggers; the axioms of the encoded ADT come with triggers */
    val inferred = chosen.toSeq.filter(_.oldTriggers.isEmpty).map(_.triggers.map(_.exps.mkString(", ")))
    assert(inferred == AstBuiltTriggerProgram.expectedTriggers)
  }
}
