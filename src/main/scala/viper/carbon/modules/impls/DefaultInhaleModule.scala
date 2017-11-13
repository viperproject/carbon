/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.impls

import viper.carbon.modules._
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.verifier.Verifier
import viper.carbon.boogie.Implicits._

/**
 * The default implementation of a [[viper.carbon.modules.InhaleModule]].

 */
class DefaultInhaleModule(val verifier: Verifier) extends InhaleModule with StatelessComponent {

  import verifier._
  import expModule._
  import stateModule._
  import mainModule._

  def name = "Inhale module"

  override def start() {
    register(this)
  }

  override def inhale(exps: Seq[sil.Exp]): Stmt = {
    (exps map (e => inhaleConnective(e.whenInhaling))) ++
      MaybeCommentBlock("Free assumptions",
        exps map (e => allFreeAssumptions(e))) ++
      assumeGoodState
  }

  def containsFunc(exp: sil.Exp): Boolean = {
    var res = false
    exp visit {
      case _: sil.FuncApp => res = true
    }
    res
  }

  /**
   * Inhales Viper expression connectives (such as logical and/or) and forwards the
   * translation of other expressions to the inhale components.
   */
  private def inhaleConnective(e: sil.Exp): Stmt = {
    e match {
      case sil.And(e1, e2) =>
        inhaleConnective(e1) ::
          inhaleConnective(e2) ::
          Nil
      case sil.Implies(e1, e2) =>
        If(translateExp(e1), inhaleConnective(e2), Statements.EmptyStmt)
      case sil.CondExp(c, e1, e2) =>
        If(translateExp(c), inhaleConnective(e1), inhaleConnective(e2))
      case sil.Let(declared,boundTo,body) if !body.isPure =>
      {
        val u = env.makeUniquelyNamed(declared) // choose a fresh binder
        env.define(u.localVar)
        Assign(translateLocalVar(u.localVar),translateExp(boundTo)) ::
          inhaleConnective(body.replace(declared.localVar, u.localVar)) ::
          {
            env.undefine(u.localVar)
            Nil
          }
      }
      case _ =>
        val stmt = components map (_.inhaleExp(e))
        if (stmt.children.isEmpty) sys.error(s"missing translation for inhaling of $e")
        (if (containsFunc(e)) Seq(assumeGoodState) else Seq()) ++ stmt ++ (if (e.isPure) Seq() else Seq(assumeGoodState))
        //(if (containsFunc(e)) assumeGoodState else Seq[Stmt]()) ++ stmt ++ (if (e.isPure) Seq[Stmt]() else assumeGoodState)
    }
  }

  override def inhaleExp(e: sil.Exp): Stmt = {
    if (e.isPure) {
      Assume(translateExp(e))
    } else {
      Nil
    }
  }
}
