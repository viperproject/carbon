package semper.carbon.modules

import semper.sil.{ast => sil}
import semper.carbon.boogie.Program

/**
 * A verifier for SIL in Carbon (defines what modules need to be available).
 *
 * @author Stefan Heule
 */
trait Verifier {
  def stmtModule: StmtModule
  def expModule: ExpModule
  def typeModule: TypeModule
  def exhaleModule: ExhaleModule
  def inhaleModule: InhaleModule
  def heapModule: HeapModule
  def funcPredModule: FuncPredModule
  def permModule: PermModule
  def mainModule: MainModule
}
