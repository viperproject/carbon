package semper.carbon.verifier

import semper.sil.{ast => sil}
import semper.carbon.modules._

/**
 * A verifier for SIL in Carbon (defines what modules need to be available).
 *
 * @author Stefan Heule
 */
trait Verifier {

  // Modules
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

  /**
   * A list of all modules.
   */
  def allModules: Seq[Module] =
    Seq(mainModule, heapModule, stmtModule, expModule, typeModule,
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
