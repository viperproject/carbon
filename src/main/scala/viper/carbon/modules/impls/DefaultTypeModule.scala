// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules.impls

import viper.carbon.modules.{StatelessComponent, TypeModule}
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.verifier.Verifier

/**
 * The default implementation of a [[viper.carbon.modules.TypeModule]].
 */
class DefaultTypeModule(val verifier: Verifier) extends TypeModule with StatelessComponent {

  import verifier._
  import heapModule._
  import domainModule._
  import permModule._
  import seqModule._
  import setModule._
  import mapModule._

  def name = "Type module"
  override def translateType(t: sil.Type): Type = {
    t match {
      case sil.Bool =>
        Bool
      case sil.Int =>
        Int
      case sil.Ref =>
        refType
      case sil.Perm =>
        permType
      case t: sil.SeqType =>
        translateSeqType(t)
      case t: sil.SetType =>
        translateSetType(t)
      case t: sil.MultisetType =>
        translateMultisetType(t)
      case t: sil.MapType =>
        translateMapType(t)
      case sil.InternalType =>
        sys.error("This is an internal type, not expected here")
      case sil.TypeVar(name) =>
        TypeVar(name)
      case t@sil.DomainType(_, _) =>
        translateDomainTyp(t)
      case sil.BackendType(boogieName, _) if boogieName != null => NamedType(boogieName)
      case sil.BackendType(_, _) => sys.error("Found non-Boogie-compatible backend type.")
      case _ => sys.error("Viper type didn't match any existing case.")
    }
  }
}
