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

  /*generates code that transfers permissions from states to used such that e can be satisfied
  * Precondition: current state is set to the used state
  * */
  def exhaleExt(states: List[Any], used:Any, e: sil.Exp, allStateAssms: Exp, RHS: Boolean = false, error: PartialVerificationError, havocHeap: Boolean = true):Stmt

  /**
    *
    * @param initBool boolean expression w which the newly generated boolean variable should be initialized
    * @param usedString string to incorporate into unique name for string
    * @param setToNew the state is set to the generated state iff this is set to true
    * @param init if this is set to true then the stmt in UsedStateSetup will initialize the states (for example
    *             masks to ZeroMask), otherwise the states contain no information
    * @return  Structure which can be used at the beginning of many operations involved in the package (Pair of
    *          the created state and the statements needed to be added to the boogie code)
    */
  def createAndSetState(initBool:Option[Exp],usedString:String = "Used",setToNew:Boolean=true,
                        init:Boolean=true):Any

  /*
  *transforms a statement such that it doesn't have any explicit assumptions anymore and all assumptions
  * are accumulated in a single variable, i.e.:
  *
  * Assume x != null
  * Assume y >= 0 is transformed to:
  * b := (b && x!= null); b := (b && y >= 0);
  */
  def exchangeAssumesWithBoolean(stmt: Stmt,boolVar: LocalVar):Stmt

  def createAndSetSumState(stateOther: Any ,boolOther:Exp,boolCur:Exp):Any

  /**
    * Preparing the execution of ghost operation by setting current state to OPS, and resetting the Union state
    */
  def prepareStmt(): Unit

  def updateUnion(): Stmt

  /**
    * To keep track of different lhs of different wands a unique ID is associated with every lhs.
    * To keep track of the closest lhs in case of nested package statements, a stack is used to keep track of lhs IDs.
    */

  /**
    * @return ID of the lhs of the closest package statement
    */
  def getActiveLhs(): Int

  /**
    * The ID given to the last lhs.
    * Note that this is different from ActiveLHS, as if we are inside a nested package statement and then exit the inner statement the lhsID is not decreased, while the activeID is now the ID of outer package statement.
    */
  def getLhsId():Int

  /**
    * Incrementing the lhsID
    */
  def incLhsId():Unit

  /**
    * Adding the lhsNum to the lhsStack
    */
  def pushLhsStack(lhsNum: Int): Unit

  /**
    * Removing the last lhsNum pushed into the stack
    */
  def popLhsStack(): Unit

  /**
    * @return the current opsState which is the state which is the result of applying the ghost operations executed so far
    */
  def getOps(): Any

  def getCurOpsBoolvar(): LocalVar


  /**
    * The temporary state connected to the current statement being evaluated inside package statement
    */
  var tempCurState: Any = null

  /**
    * The union of opsState and tempState connected to the current statement being evaluated
    */
  var UNIONState: Any = null

  /**
    * wandId == 0 ==> Outside a package statement
    * wandId == 1 ==> inside a package statement
    * wandId == 2 ==> inside a package statement nested inside another package statement
    */
  var wandId: Int = 0

  // ftsm == 0   ==>   returns ft representation
  // ftsm == 1   ==>   returns sm representation
  def getWandFtSmRepresentation(wand: sil.MagicWand, ftsm: Int): Exp
}
