package viper.carbon.modules

/**
 * Created by Gaurav on 06.03.2015.
 */

import viper.carbon.modules.components.{ComponentRegistry, TransferComponent}
import viper.silver.verifier.PartialVerificationError
import viper.silver.{ast => sil}
import viper.carbon.boogie.{Exp, LocalVar, Stmt, TrueLit}
import viper.silver.ast.Seqn


trait WandModule extends Module with ComponentRegistry[TransferComponent] {
  def translatePackage(p: sil.Package, error: PartialVerificationError, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false):Stmt

  def getWandRepresentation(w: sil.MagicWand):Exp

  def translateApply(p: sil.Apply, error: PartialVerificationError, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false):Stmt

  def exhaleExt(states: List[Any], used:Any, e: sil.Exp, allStateAssms: Exp, RHS: Boolean = false, error: PartialVerificationError):Stmt

  def createAndSetState(initBool:Option[Exp],usedString:String = "Used",setToNew:Boolean=true,
                        init:Boolean=true):Any

  def exchangeAssumesWithBoolean(stmt: Stmt,boolVar: LocalVar):Stmt

  def createAndSetSumState(stateOther: Any ,boolOther:Exp,boolCur:Exp):Any

  var tempCurState: Any = null

  var UNIONState: Any = null
  }
