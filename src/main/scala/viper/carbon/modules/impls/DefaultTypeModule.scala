/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package semper.carbon.modules.impls

import semper.carbon.modules.TypeModule
import semper.sil.{ast => sil}
import semper.carbon.boogie._
import semper.carbon.verifier.Verifier

/**
 * The default implementation of a [[semper.carbon.modules.TypeModule]].
 */
class DefaultTypeModule(val verifier: Verifier) extends TypeModule {

  import verifier._
  import heapModule._
  import domainModule._
  import permModule._
  import seqModule._
  import setModule._

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
      case t@sil.SeqType(elemType) =>
        translateSeqType(t)
      case t@sil.SetType(elemType) =>
        translateSetType(t)
      case t@sil.MultisetType(elemType) =>
        translateMultisetType(t)
      case sil.Pred =>
        sys.error("this is an internal type, not expected here")
      case sil.TypeVar(name) =>
        TypeVar(name)
      case t@sil.DomainType(_, _) =>
        translateDomainTyp(t)
    }
  }
}
