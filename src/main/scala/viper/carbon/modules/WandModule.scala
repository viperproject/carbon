// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules

/**
 * Created by Gaurav on 06.03.2015.
 */

import viper.carbon.modules.components.{ComponentRegistry, TransferComponent}
import viper.silver.verifier.PartialVerificationError
import viper.silver.{ast => sil}
import viper.carbon.boogie.{Exp, LocalVar, Stmt, TrueLit}


trait WandModule extends Module with ComponentRegistry[TransferComponent] {

  /*====================================================================== General Note ======================================================================
    Statements being translated inside package statements are handled differently in two ways:
    exhaling: The permissions are exhaled from many states (the global current state, lhs state ...) instead of just one state.
    inhaling: Every state has a boolean expression (state boolean) that represents assumptions about this state and assumptions are added as
              conjunctions to these booleans (e.g., having a state 'Si' and its boolean is 'Bi', inhale x == 2 is translated as Bi = Bi & x == 2).
    Therefore, whenever a method is used to translate both statements inside and outside a package statement it will has the following parameters:
    statesStackForPackageStmt: A stack of states from which permissions can be exhaled during a package statement (instead of exhaling from only one state).
    allStateAssms: The conjunction of all state booleans of the states on states stack. Used in evaluating expressions and assertions.
    insidePackageStmt: A flag that indicates if the statement being translated is inside a package statement or not
    ==========================================================================================================================================================
   */




  var tempCurState: Any = null  // A temporary state that is used to execute statements inside a package statement (e.g., collecting needed permissions)

  var UNIONState: Any = null // The union of opsState (the resulting state from executing the ghost operations so far) and
                            // tempCurState. All Evaluations of expressions during translating the package statement take place in this UNIONState.

  /**
    * Represents the nesting depth of package statements for the current statement being translated, e.g.,
    * nestingDepth == 0 means the current statement being translated is outside a package statement
    * nestingDepth == 1 means the current statement being translated is inside a package statement (only one package statement)
    * nestingDepth == 2 means the current statement being translated is inside a package statement nested inside another package statement
    */
  var nestingDepth: Int = 0



  /**
    * The method responsible for translating a package statement to the corresponding Boogie statement
    * the 'statesStackForPackageStmt', 'allStateAssms' and 'insidePackageStmt' parameters are used to translate nested package statements.
    * @param p the package statement to be translated.
    * @param statesStackForPackageStmt the stack of states for the outer package statements in case of nested package statements.
    * @param allStateAssms  the conjunction of all states booleans on the states stack (assumption about states resulted from executing the outer package statements).
    * @param insidePackageStmt boolean represents whether this function is being called during another package statement or not.
    * @return
    */
  def translatePackage(p: sil.Package, error: PartialVerificationError, statesStackForPackageStmt: List[Any] = null, allStateAssms: Exp = TrueLit(), insidePackageStmt: Boolean = false):Stmt

  def getWandRepresentation(w: sil.MagicWand):Exp

  /**
    * Translates the 'apply' statements to the corresponding Boogie statements
    * the 'statesStackForPackageStmt', 'allStateAssms' and 'insidePackageStmt' parameters are used when being called inside a package statement
    */
  def translateApply(p: sil.Apply, error: PartialVerificationError, statesStackForPackageStmt: List[Any] = null, allStateAssms: Exp = TrueLit(), insidePackageStmt: Boolean = false):Stmt


  /**
    * exhales an expression 'e' from a stack of states 'states'. The permissions can be collected from different states on 'states' stack. So, the permissions are
    * transfered first to 'used' state to keep track of these permissions and then exhaled from the 'used' state.
    * @param states Stack of states from which the expression 'e' is exhaled
    * @param used a state that is used to keep track of the permissions being removed from the 'states' stack
    * @param e the expression to be exhaled
    * @param allStateAssms The assumptions about all states on the 'states' stack. Used in evaluating the expressions.
    * @param RHS boolean indicating if the currently translated statement is in the RHS of the wand or a ghost operation
    * @param error the raised error if the exhaling failed
    * @param havocHeap boolean that controls havocing the heap after the exhale or not
    * @return the boogie code for the behavior described above.
    */
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

  /**
    * create a state Result which is the union of two states. The first state is taken from the given parameters 'state Other'
    * while the other state is the current state.
    * @param stateOther The state which will be added to the current state
    * @param boolOther State boolean carrying the assumptions of the other state
    * @param boolCur State boolean carrying the assumptions of the curretn state
    * @return Boogie statement for executing the union.
    */
  def createAndSetSumState(stateOther: Any ,boolOther:Exp,boolCur:Exp):Any

  /**
    * Called before executing any statement inside a package statement. It performs the needed initializations for the execution of a ghost operation.
    * (e.g., Initializing the states used such as 'ops-state' and 'union-state').
    */
  def translatingStmtsInWandInit(): Unit

  /**
    * When opsState or tempCurState are changed, the UNIONState is updated to be the union of both.
    * The union state is used in evaluating expressions during a package statement
    */
  def updateUnion(): Stmt


  /*=============================================================================================================
    The following part is for supporting 'old(lhs)' during package statements.
    Having nested package statements, old(lhs) refers to the closest package statement in which old(lhs) exists.
    Every package statement gets an identifiers 'ID' so it can be referred to when translating old(lhs). Identifiers
    for active package statements are kept in a stack 'activeWandsStack' so we can refer to the last (closest)
    package statement.
    =============================================================================================================
   */

  /**
    * @return The identifier 'ID' of the closest package statement (top of 'activeWandsStack')
    */
  def getActiveLhs(): Int

  /**
    * @return a new identifier to be given to the lhs of a new package statement to be referred to later
    */
  def getNewLhsID():Int

  /**
    * Adding a new identifier to 'activeWandsStack'
    */
  def pushToActiveWandsStack(lhsID: Int): Unit

  /**
    * Removing the the top of 'activeWandsStack' (the innermost package statement in case of having nested package statement)
    */
  def popFromActiveWandsStack(): Unit



  /*=============================================================================================================
   Some getters for wandModule variables
   =============================================================================================================
  */
  /**
    * @return opsState: The state resulting from executing the ghost operations so far.
    */
  def getOps(): Any

  /**
    * @return state boolean for the current ops-state (representing the assumptions about this state)
    */
  def getCurOpsBoolvar(): LocalVar


  /**
    * Used in snapshots of magic wands. It returns a boogie function that refers to wand footprint or wand secondary mask
    * @param wand the magic wand that we need to refer to its footprint or its secondary mask
    * @param ftsm boolean specifying if the methor returns the footprint of the wand (wand#ft) function or secondray mask (wand#sm) function.
    * @return
    * ftsm == 1   ==>   returns sm representation (wand#sm)
    * ftsm == 0   ==>   returns ft representation (wand#ft)
    */
  def getWandFtSmRepresentation(wand: sil.MagicWand, ftsm: Int): Exp
}
