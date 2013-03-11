package semper.carbon.modules

import semper.sil.{ast => sil}

/**
 * A verifier for SIL in Carbon (defines what modules need to be available).
 *
 * @author Stefan Heule
 */
trait Verifier {
  /**
   * The full command used to invoke this verification
   */
  def fullCmd: String

  /**
   * The tool (including version) used for this translation.
   */
  def toolDesc: String

  /**
   * A descriptive string for every dependency
   */
  def dependencyDescs: Seq[String]

  /**
   * A list of all modules.
   */
  def allModules: Seq[Module] =
    Seq(mainModule, heapModule, stmtModule, expModule, typeModule,
      exhaleModule, inhaleModule, funcPredModule, permModule)

  def mainModule: MainModule
  def heapModule: HeapModule
  def stmtModule: StmtModule
  def expModule: ExpModule
  def typeModule: TypeModule
  def exhaleModule: ExhaleModule
  def inhaleModule: InhaleModule
  def funcPredModule: FuncPredModule
  def permModule: PermModule
}
