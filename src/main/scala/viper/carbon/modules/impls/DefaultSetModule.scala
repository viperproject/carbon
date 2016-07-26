/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.carbon.modules.impls

import viper.carbon.modules.SetModule
import viper.silver.components.StatefulComponent
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.verifier.Verifier
import viper.carbon.boogie.Implicits._
import viper.carbon.modules.impls.dafny_axioms.SetAxiomatization
import viper.carbon.modules.components.DefinednessComponent

/**
 * The default implementation of [[viper.carbon.modules.SetModule]].

 */
class DefaultSetModule(val verifier: Verifier)
    extends SetModule
    with DefinednessComponent {
  import verifier._
  import typeModule._
  import expModule._

  /**
   * Have sets been used so far (to determine if we need to include
   * the set axiomatization in the prelude.
   */
  private var used = false

  def name = "Set module"
  implicit val namespace = verifier.freshNamespace("set")

  override def freeAssumptions(e: sil.Exp): Stmt = {
    e match {
      case _ if e.typ.isInstanceOf[sil.MultisetType] =>
        Assume(FuncApp(Identifier("$IsGoodMultiSet"),translateExp(e),Bool))
      case _ => Nil
    }
  }

  override def validValue(typ: sil.Type, variable: LocalVar, isParameter: Boolean): Option[Exp] = {
    if (typ.isInstanceOf[sil.MultisetType]) Some(FuncApp(Identifier("$IsGoodMultiSet"),variable,Bool)) else None
  }

  override def preamble = {
    if (used) {
      LiteralDecl(SetAxiomatization.value)
    } else {
      Nil
    }
  }

  override def translateSetExp(e: sil.Exp): Exp = {
    def t(e: sil.Exp) = translateExp(e)
    val isMultiset = ((x:sil.Exp) => x.typ match {
      case _: sil.MultisetType => true
      case _: sil.SetType => false
      case _ => sys.error("Internal Error: expression " + e + "was expected to be of Set or Multiset type")
    })
    used = true
    val typ = translateType(e.typ)
    e match {
      case sil.EmptySet(elemTyp) =>
        val fa = FuncApp(Identifier("Set#Empty"), Nil, typ)
        fa.showReturnType = true // needed (in general) to avoid Boogie complaints about ambiguous type variable
        fa
      case sil.ExplicitSet(elems) =>
        def buildSet(es: Seq[sil.Exp]): Exp = {
          es.toList match {
            case Nil => sys.error("did not expect empty sequence")
            case a :: Nil =>
              FuncApp(Identifier("Set#Singleton"), t(a), typ)
            case a :: as =>
              FuncApp(Identifier("Set#UnionOne"), List(buildSet(as), t(a)), typ)
          }
        }
        buildSet(elems)
      case sil.EmptyMultiset(elemTyp) =>
        val fa = FuncApp(Identifier("MultiSet#Empty"), Nil, typ)
        fa.showReturnType = true // needed (in general) to avoid Boogie complaints about ambiguous type variable
        fa
      case sil.ExplicitMultiset(elems) =>
        def buildSet(es: Seq[sil.Exp]): Exp = {
          es.toList match {
            case Nil => sys.error("did not expect empty sequence")
            case a :: Nil =>
              FuncApp(Identifier("MultiSet#Singleton"), t(a), typ)
            case a :: as =>
              FuncApp(Identifier("MultiSet#UnionOne"), List(buildSet(as), t(a)), typ)
          }
        }
        buildSet(elems)
      case sil.AnySetUnion(left, right) =>
        if (isMultiset(e)) FuncApp(Identifier("MultiSet#Union"), List(t(left), t(right)), typ)
        else FuncApp(Identifier("Set#Union"), List(t(left), t(right)), typ)
      case sil.AnySetIntersection(left, right) =>
        if (isMultiset(e)) FuncApp(Identifier("MultiSet#Intersection"), List(t(left), t(right)), typ)
        else FuncApp(Identifier("Set#Intersection"), List(t(left), t(right)), typ)
      case sil.AnySetSubset(left, right) =>
        if (isMultiset(left)) FuncApp(Identifier("MultiSet#Subset"), List(t(left), t(right)), Bool)
        else FuncApp(Identifier("Set#Subset"), List(t(left), t(right)), Bool)
      case sil.AnySetMinus(left, right) =>
        if (isMultiset(e)) FuncApp(Identifier("MultiSet#Difference"), List(t(left), t(right)), typ)
        else FuncApp(Identifier("Set#Difference"), List(t(left), t(right)), typ)
      case sil.AnySetContains(left, right) =>
        if (isMultiset(right))
          MapSelect(t(right),Seq(t(left)))
         // FuncApp(Identifier("MultiSet#Subset"), List(FuncApp(Identifier("MultiSet#Singleton"), List(t(left)), typ), t(right)), Bool)
        else
          MapSelect(t(right),Seq(t(left)))
          //FuncApp(Identifier("Set#Subset"), List(FuncApp(Identifier("Set#Singleton"), List(t(left)), typ), t(right)), Bool)
      case sil.AnySetCardinality(set) =>
        if (isMultiset(set)) FuncApp(Identifier("MultiSet#Card"), t(set), Bool)
        else FuncApp(Identifier("Set#Card"), t(set), Bool)
      case sil.EqCmp(left, right) =>
        if (isMultiset(left)) FuncApp(Identifier("MultiSet#Equal"), List(t(left), t(right)), Bool)
        else FuncApp(Identifier("Set#Equal"), List(t(left), t(right)), Bool)
      case sil.NeCmp(left, right) =>
        if (isMultiset(left)) UnExp(Not, FuncApp(Identifier("MultiSet#Equal"), List(t(left), t(right)), Bool))
        else UnExp(Not, FuncApp(Identifier("Set#Equal"), List(t(left), t(right)), Bool))
      case _ => sys.error("not a set expression")
    }
  }

  override def translateSetType(setType: sil.SetType): Type = {
    used = true
    NamedType("Set", translateType(setType.elementType))
  }

  override def translateMultisetType(setType: sil.MultisetType): Type = {
    used = true
    NamedType("MultiSet", translateType(setType.elementType))
  }

  /**
   * Reset the state of this module so that it can be used for new program. This method is called
   * after verifier gets a new program.
   */
  override def reset(): Unit = {
    used = false
  }
}
