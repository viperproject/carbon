package semper.carbon.verifier

import semper.sil.{ast => sil}
import semper.carbon.modules._

/**
 * A verifier for SIL in Carbon (defines what modules need to be available).
 *
 * @author Stefan Heule
 */
trait Verifier {

  // All modules
  // Note: we use vals to make it possible to import methods from other modules for
  // convenience.
  val mainModule: MainModule
  val heapModule: HeapModule
  val stateModule: StateModule
  val stmtModule: StmtModule
  val expModule: ExpModule
  val typeModule: TypeModule
  val exhaleModule: ExhaleModule
  val inhaleModule: InhaleModule
  val funcPredModule: FuncPredModule
  val permModule: PermModule

  /**
   * A list of all modules.
   */
  def allModules: Seq[Module] =
    Seq(mainModule, stateModule, heapModule, stmtModule, expModule, typeModule,
      exhaleModule, inhaleModule, funcPredModule, permModule)

  /**
   * Debug information (e.g., the full command used to invoke this verification).
   */
  def debugInfo: Seq[(String, Any)]

  /**
   * The tool (including version) used for this translation.
   */
  def toolDesc: String

  /**
   * A descriptive string for every dependency
   */
  def dependencyDescs: Seq[String]
}
