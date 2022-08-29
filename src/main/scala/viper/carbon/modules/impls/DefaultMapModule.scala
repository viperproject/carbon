// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules.impls

import viper.carbon.boogie._
import viper.carbon.modules.MapModule
import viper.carbon.modules.components.DefinednessComponent
import viper.carbon.modules.impls.map_axioms.MapAxiomatization
import viper.carbon.verifier.Verifier
import viper.silver.verifier.{PartialVerificationError, reasons}
import viper.silver.{ast => sil}

class DefaultMapModule(val verifier: Verifier) extends MapModule with DefinednessComponent {
  import verifier._
  import typeModule._
  import expModule._
  import DefaultMapModule._

  /** The name of this module. */
  override def name: String = "Map module"

  implicit val namespace = verifier.freshNamespace("map")

  /** Have maps been used so far (to determine if we need to include the set axiomatisation in the prelude). */
  private var used = false

  override def isUsed() : Boolean = used

  override def preamble : Seq[Decl] =
    if (used) Seq(LiteralDecl(MapAxiomatization.value)) else Seq()

  override def start() : Unit = expModule.register(this)

  override def translateMapExp(exp : sil.Exp) : Exp = {
    used = true

    def rec(e : sil.Exp) = translateExp(e) // recurse
    val typ = translateType(exp.typ)

    exp match {
      case _: sil.EmptyMap => {
        val fa = FuncApp(Identifier(mapEmptyOpName), Nil, typ)
        fa.showReturnType = true // needed (in general) to avoid Boogie complaints about ambiguous type variable
        fa
      }

      case exp: sil.ExplicitMap =>
        translateMapExp(exp.desugared) // desugar into a series of map updates starting from an empty map
      case sil.MapCardinality(base) =>
        FuncApp(Identifier(mapCardOpName), Seq(rec(base)), Int)
      case sil.MapDomain(base) =>
        FuncApp(Identifier(mapDomainOpName), Seq(rec(base)), typ)
      case sil.MapRange(base) =>
        FuncApp(Identifier(mapValuesOpName), Seq(rec(base)), typ)
      case sil.MapUpdate(base, key, value) =>
        FuncApp(Identifier(mapBuildOpName), Seq(rec(base), rec(key), rec(value)), typ)
      case exp: sil.MapContains =>
        translateExp(exp.desugared)
      case sil.EqCmp(left, right) =>
        FuncApp(Identifier(mapEqualOpName), List(rec(left), rec(right)), typ)
      case sil.NeCmp(left, right) =>
        UnExp(Not, FuncApp(Identifier(mapEqualOpName), List(rec(left), rec(right)), typ))

      case sil.MapLookup(base, key) => base.typ match {
        case sil.MapType(keyType, valueType) => {
          val mTyp = MapType(Seq(translateType(keyType)), translateType(valueType))
          val mExp = FuncApp(Identifier(mapElementsOpName), Seq(rec(base)), mTyp)
          MapSelect(mExp, Seq(rec(key)))
        }
        case t => sys.error(s"expected a map type, but found $t")
      }

      case _ => sys.error("not a map expression")
    }
  }

  override def translateMapType(mapType : sil.MapType) : Type = {
    used = true
    NamedType("Map", Seq(translateType(mapType.keyType), translateType(mapType.valueType)))
  }

  override def simplePartialCheckDefinednessAfter(exp: sil.Exp, error: PartialVerificationError, makeChecks: Boolean): Stmt = {
    if (makeChecks) exp match {
      case sil.MapLookup(base, key) => {
        val containsExp = translateMapExp(sil.MapContains(key, base)(exp.pos, exp.info, exp.errT))
        Assert(containsExp, error.dueTo(reasons.MapKeyNotContained(base, key)))
      }
      case _ => Statements.EmptyStmt
    }
    else Statements.EmptyStmt
  }

  override def reset() : Unit = used = false
}

object DefaultMapModule {
  private def opName(name : String) = s"Map#$name"

  val mapBuildOpName : String = opName("Build")
  val mapCardOpName : String = opName("Card")
  val mapDomainOpName : String = opName("Domain")
  val mapElementsOpName : String = opName("Elements")
  val mapEmptyOpName : String = opName("Empty")
  val mapEqualOpName : String = opName("Equal")
  val mapValuesOpName : String = opName("Values")
}