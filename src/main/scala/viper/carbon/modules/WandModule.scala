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
  /**
    * 'statesStack', 'allStateAssms' and 'inWand' are used in the case of 'translatePackage' being called during a package statement (nested package statements).
    *
    * statesStack is the stack of states used during packaging the outer magic wand (it carries the 'current' state, left-hand side state of the outer wand).
    *
    * inWand distinguishes whether this method is called during a package statement or not.
    *
    * allStateAssms is a boolean expression that carries the conjunction for all the assumptions made about all states on statesStack
    */
  def translatePackage(p: sil.Package, error: PartialVerificationError, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false):Stmt

  def getWandRepresentation(w: sil.MagicWand):Exp

  def translateApply(p: sil.Apply, error: PartialVerificationError, statesStack: List[Any] = null, allStateAssms: Exp = TrueLit(), inWand: Boolean = false):Stmt

  /*generates code that transfers permissions from states to 'used' such that e can be satisfied in the 'used' state.
  * The permissions transferred are removed from the states on 'states' and added to 'used' state.
  * Precondition: current state is set to the 'used' state
  * */
  def exhaleExt(states: List[Any], used:Any, e: sil.Exp, allStateAssms: Exp, RHS: Boolean = false, error: PartialVerificationError, havocHeap: Boolean = true):Stmt

  /**
    * This method creates a new state and sets it as the current state. The following parameters help customize the newly created state.
    * @param initBool boolean expression w which the newly generated boolean variable should be initialized
    * @param usedString string to incorporate into unique name for string
    * @param setToNew the state is set to the generated state iff this is set to true
    * @param init if this is set to true then the stmt in UsedStateSetup will initialize the states (for example
    *             masks to ZeroMask), otherwise the states contain no information
    * This method returns a structure (StateModule.StateSetup) which can be used at the beginning of many operations involved in the package (Pair of
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

  //create a state Result which is the union of the 'currentState'  and 'stateOther'. It calls a helper method with the same name but different signature.
  // More explanation can be found at the documentation of the helper method in the DefaultWandModule.
  def createAndSetSumState(stateOther: Any ,boolOther:Exp,boolCur:Exp):Any

  /**
    * Preparing the execution of a ghost operation by setting current state to wandModule.OPS, and resetting the wandModule.UNIONState
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
    * Represents the depth of package statements for the current statement being translated, e.g.,
    * wandId == 0 means the current statement being translated is outside a package statement
    * wandId == 1 means the current statement being translated is inside a package statement (only one package statement, i.e, not nested)
    * wandId == 2 means means the current statement being translated is inside a package statement nested inside another package statement
    */
  var wandId: Int = 0

  // ftsm == 0   ==>   returns ft representation (wand#ft)
  // ftsm == 1   ==>   returns sm representation (wand#sm)
  def getWandFtSmRepresentation(wand: sil.MagicWand, ftsm: Int): Exp
}
