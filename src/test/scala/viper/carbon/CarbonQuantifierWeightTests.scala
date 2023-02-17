// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

import org.scalatest.BeforeAndAfterAll
import org.scalatest.funsuite.AnyFunSuite
import viper.carbon.boogie.PrettyPrinter
import viper.carbon.verifier.Environment
import viper.carbon.CarbonVerifier
import viper.silver.ast.{Add, AnonymousDomainAxiom, Domain, DomainFunc, DomainFuncApp, EqCmp, Exists, Forall, Int, IntLit, LocalVar, LocalVarDecl, Method, Program, Seqn, Trigger, TrueLit, WeightedQuantifier}
import viper.silver.reporter.NoopReporter
import viper.silver.verifier.{Failure, Success}

class CarbonQuantifierWeightTests extends AnyFunSuite with BeforeAndAfterAll {
  val carbon: CarbonVerifier = CarbonVerifier(NoopReporter)

  override def beforeAll() {
    carbon.parseCommandLine(Seq("dummy.vpr"))
    carbon.start()
  }

  override def afterAll() {
    carbon.stop()
  }

  test("The quantifier weight inhibits instantiations") {
    def verifyUsingWeight(weight: Int) = {
      val domainName = "MyDomain"
      val xDecl = LocalVarDecl("x", Int)()
      val x = LocalVar("x", Int)()
      val f = DomainFunc("f", Seq(xDecl), Int)(domainName = domainName)
      val axiom = AnonymousDomainAxiom(Forall(
        Seq(xDecl),
        Seq(Trigger(Seq(DomainFuncApp(f, Seq(x), Map())()))()),
        EqCmp(DomainFuncApp(f, Seq(Add(x, IntLit(1)())()), Map())(), IntLit(42)())(),
      )(
        // Set the weight of the quantifier
        info = WeightedQuantifier(weight)
      ))(domainName = domainName)
      val domain = Domain(domainName, Seq(f), Seq(axiom))()
      val pre = EqCmp(DomainFuncApp(f, Seq(IntLit(0)()), Map())(), IntLit(42)())()
      val post = EqCmp(DomainFuncApp(f, Seq(IntLit(50)()), Map())(), IntLit(42)())()
      val method = Method("test", Seq(LocalVarDecl("x", Int)()), Seq(), Seq(pre), Seq(post), Some(Seqn(Seq(), Seq())()))()
      val program = Program(Seq(domain), Seq(), Seq(), Seq(), Seq(method), Seq())()
      carbon.verify(program)
    }

    // A small weight should allow the axiom to be instantiated
    verifyUsingWeight(1) match {
      case Success => // Ok
      case Failure(errors) => assert(false)
    }

    // A big weight should prevent the axiom from being instantiated
    verifyUsingWeight(999) match {
      case Success => assert(false)
      case Failure(errors) => // Ok
    }
  }
}
