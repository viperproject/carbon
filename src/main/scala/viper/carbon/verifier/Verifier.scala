// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.verifier

import viper.silver.{ast => sil}
import viper.carbon.modules._
import viper.carbon.boogie.Namespace

/**
 * A verifier for Viper in Carbon (defines what modules need to be available).
 */
trait Verifier {

  // All modules
  // Note: we use vals to make it possible to import methods from other modules for
  // convenience.
  def mainModule: MainModule
  def heapModule: HeapModule
  def stateModule: StateModule
  def stmtModule: StmtModule
  def expModule: ExpModule
  def typeModule: TypeModule
  def exhaleModule: ExhaleModule
  def inhaleModule: InhaleModule
  def funcPredModule: FuncPredModule
  def permModule: PermModule
  def domainModule: DomainModule
  def seqModule: SeqModule
  def setModule: SetModule
  def mapModule: MapModule
  def wandModule: WandModule
  def loopModule: LoopModule

  /**
   * A list of all modules.
   */
  def allModules: Seq[Module] = {
    Seq(mainModule, stateModule, heapModule, permModule, stmtModule, expModule, typeModule,
      exhaleModule, inhaleModule, funcPredModule, domainModule, seqModule, setModule,
      loopModule, mapModule, wandModule)
  } ensuring {
    mods => true
  }

  /**
   * Debug information (e.g., the full command used to invoke this verification).
   */
  def getDebugInfo: Seq[(String, Any)]

  /**
   * The tool (including version) used for this translation.
   */
  def toolDesc: String

  /**
   * A descriptive string for every dependency
   */
  def dependencyDescs: Seq[String]

  /**
   * Create a new namespace with a unique ID.
   */
  def freshNamespace(name: String): Namespace

  /**
   * The program currently being verified.
   */
  def program: sil.Program

  /**
   *  Replace the program with the provided one (for instance, to achieve whole-program transformations, including updating lookups of method definitions etc.)
   */
  def replaceProgram(prog : sil.Program): Unit

  def assumeInjectivityOnInhale: Boolean

  def usePolyMapsInEncoding: Boolean

}
