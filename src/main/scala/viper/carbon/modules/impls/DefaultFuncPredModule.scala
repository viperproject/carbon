// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.carbon.modules.impls

import viper.carbon.boogie.Bool
import viper.carbon.boogie.CondExp
import viper.carbon.boogie.Exp
import viper.carbon.boogie.FalseLit
import viper.carbon.boogie.Forall
import viper.carbon.boogie.If
import viper.carbon.boogie.Int
import viper.carbon.boogie.IntLit
import viper.carbon.boogie.LocalVar
import viper.carbon.boogie.LocalVarDecl
import viper.carbon.boogie.Stmt
import viper.carbon.boogie.Trigger
import viper.carbon.boogie.TypeVar
import viper.carbon.modules._
import viper.silver.ast.{FuncApp => silverFuncApp}
import viper.silver.ast.utility.Expressions.{contains, whenExhaling, whenInhaling}
import viper.silver.ast.{NoPerm, PermGtCmp, PredicateAccess, PredicateAccessPredicate, Unfolding}
import viper.silver.{ast => sil}
import viper.carbon.boogie._
import viper.carbon.verifier.{Environment, Verifier}
import viper.carbon.boogie.Implicits._
import viper.silver.ast.utility._
import viper.carbon.modules.components.{DefinednessComponent, ExhaleComponent, InhaleComponent}
import viper.silver.verifier.{NullPartialVerificationError, PartialVerificationError, errors}

import scala.collection.mutable.ListBuffer
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion

import scala.collection.mutable

/**
 * The default implementation of a [[viper.carbon.modules.FuncPredModule]].
 */
class DefaultFuncPredModule(val verifier: Verifier) extends FuncPredModule
with DefinednessComponent with ExhaleComponent with InhaleComponent {
  def name = "Function and predicate module"

  import verifier._
  import typeModule._
  import mainModule._
  import stateModule._
  import expModule._
  import exhaleModule._
  import inhaleModule._
  import heapModule._
  import permModule._

  implicit val fpNamespace = verifier.freshNamespace("funcpred")

  /* Maps function names to their height.
   * Previously mapped Function AST nodes to their height, but this prevents looking up functions
   * with quantifiers whose triggers (i.e. via auto-triggering) have been changed in between
   * populating the map and looking up a function height.
   */
  private var heights: Map[String, Int] = null
  private var checkingDefinednessOfFunction: Option[String] = None // used to flag special behaviour when checking function definitions

  private val assumeFunctionsAboveName = Identifier("AssumeFunctionsAbove")
  private val assumeFunctionsAbove: Const = Const(assumeFunctionsAboveName)
  private val specialRefName = Identifier("special_ref")
  private val specialRef = Const(specialRefName)
  private val limitedPostfix = "'"
  private val triggerFuncPostfix = "#trigger"
  private val triggerFuncNoHeapPostfix = "#triggerStateless"
  private val framePostfix = "#frame"
  private val frameTypeName = "FrameType"
  private val frameType = NamedType(frameTypeName)
  private val emptyFrameName = Identifier("EmptyFrame")
  private val emptyFrame = Const(emptyFrameName)
  private val combineFramesName = Identifier("CombineFrames")
  private val frameFragmentName = Identifier("FrameFragment")
  private val condFrameName = Identifier("ConditionalFrame")
  private val dummyTriggerName = Identifier("dummyFunction")
  private val resultName = Identifier("Result")
  private val insidePredicateName = Identifier("InsidePredicate")

  private var qpPrecondId = 0
  private var qpCondFuncs: ListBuffer[(Func,sil.Forall)] = new ListBuffer[(Func, sil.Forall)]();

  type FrameInfos = collection.mutable.HashMap[String,(Exp, StateSnapshot, Seq[LocalVarDecl], Seq[(Func, sil.Forall)])]
  val FrameInfos = collection.mutable.HashMap

  private var functionFrames : FrameInfos = FrameInfos();
  private var predicateFrames: FrameInfos = FrameInfos();

  override def preamble = {
    val fp = if (verifier.program.functions.isEmpty) Nil
    else {
      val m = heights.values.max
      DeclComment("Function heights (higher height means its body is available earlier):") ++
        (for (i <- m to 0 by -1) yield {
          val fs = heights filter (p => p._2 == i) map (_._1)
          DeclComment(s"- height $i: ${fs.mkString(", ")}")
        }) ++
        ConstDecl(assumeFunctionsAboveName, Int)
    }
    fp ++
      CommentedDecl("Declarations for function framing",
        TypeDecl(frameType) ++
          ConstDecl(emptyFrameName, frameType) ++
          Func(frameFragmentName, Seq(LocalVarDecl(Identifier("t"), TypeVar("T"))), frameType) ++
          Func(condFrameName, Seq(LocalVarDecl(Identifier("p"), permType), LocalVarDecl(Identifier("f"), frameType)), frameType) ++
          Func(dummyTriggerName, Seq(LocalVarDecl(Identifier("t"), TypeVar("T"))), Bool) ++
          Func(combineFramesName,
            Seq(LocalVarDecl(Identifier("a"), frameType), LocalVarDecl(Identifier("b"), frameType)),
            frameType), size = 1) ++
      CommentedDecl("Definition of conditional frame fragments", {
        val params = Seq(LocalVarDecl(Identifier("p"), permType), LocalVarDecl(Identifier("f"), frameType))
        val condFrameApp = FuncApp(condFrameName, params map (_.l), frameType)
        Axiom(Forall(params, Trigger(condFrameApp),
          condFrameApp === CondExp(LocalVar(Identifier("p"), permType) > RealLit(0),LocalVar(Identifier("f"), frameType), emptyFrame)
        ))
      }
      ) ++
      CommentedDecl("Function for recording enclosure of one predicate instance in another",
        Func(insidePredicateName,
          Seq(
            LocalVarDecl(Identifier("p"), predicateVersionFieldType("A")),
            LocalVarDecl(Identifier("v"), predicateVersionType),
            LocalVarDecl(Identifier("q"), predicateVersionFieldType("B")),
            LocalVarDecl(Identifier("w"), predicateVersionType)
          ),
          Bool), size = 1) ++
      CommentedDecl(s"Transitivity of ${insidePredicateName.name}", {
        val vars1 = Seq(
          LocalVarDecl(Identifier("p"), predicateVersionFieldType("A")),
          LocalVarDecl(Identifier("v"), predicateVersionType)
        )
        val vars2 = Seq(
          LocalVarDecl(Identifier("q"), predicateVersionFieldType("B")),
          LocalVarDecl(Identifier("w"), predicateVersionType)
        )
        val vars3 = Seq(
          LocalVarDecl(Identifier("r"), predicateVersionFieldType("C")),
          LocalVarDecl(Identifier("u"), predicateVersionType)
        )
        val f1 = FuncApp(insidePredicateName, (vars1 ++ vars2) map (_.l), Bool)
        val f2 = FuncApp(insidePredicateName, (vars2 ++ vars3) map (_.l), Bool)
        val f3 = FuncApp(insidePredicateName, (vars1 ++ vars3) map (_.l), Bool)
        Axiom(
          Forall(
            vars1 ++ vars2 ++ vars3,
            Trigger(Seq(f1, f2)),
            (f1 && f2) ==> f3
          )
        )
      }, size = 1) ++
      CommentedDecl(s"Knowledge that two identical instances of the same predicate cannot be inside each other", {
        val p = LocalVarDecl(Identifier("p"), predicateVersionFieldType())
        val vars = Seq(
          p,
          LocalVarDecl(Identifier("v"), predicateVersionType),
          p,
          LocalVarDecl(Identifier("w"), predicateVersionType)
        )
        val f = FuncApp(insidePredicateName, vars map (_.l), Bool)
        Axiom(
          Forall(
            vars.distinct,
            Trigger(f),
            UnExp(Not, f)
          )
        )
      }, size = 1)
  }

  override def start() {
    expModule.register(this)
    inhaleModule.register(this, before = Seq(verifier.inhaleModule)) // this is because of inhaleExp definition, which tries to add extra information from executing the unfolding first
    exhaleModule.register(this, before = Seq(verifier.exhaleModule)) // this is because of exhaleExp definition, which tries to add extra information from executing the unfolding first
  }

  def reset() = {
    heights = Functions.heights(verifier.program).map{case (f, h) => f.name -> h}
    tmpStateId = -1
    duringFold = false
    foldInfo = null
    duringUnfold = false
    duringUnfolding = false
    duringUnfoldingExtraUnfold = false
    unfoldInfo = null
    exhaleTmpStateId = -1
    extraUnfolding = false
    functionFrames = FrameInfos()
    predicateFrames = FrameInfos()
  }

    override def translateFunction(f: sil.Function, names: Option[mutable.Map[String, String]]): Seq[Decl] = {
    env = Environment(verifier, f)
    ErrorMemberMapping.currentMember = f
    val res = MaybeCommentedDecl(s"Translation of function ${f.name}",
      MaybeCommentedDecl("Uninterpreted function definitions", functionDefinitions(f), size = 1) ++
        (if (f.isAbstract) Nil else
        MaybeCommentedDecl("Definitional axiom", definitionalAxiom(f), size = 1)) ++
        MaybeCommentedDecl("Framing axioms", framingAxiom(f), size = 1) ++
        MaybeCommentedDecl("Postcondition axioms", postconditionAxiom(f), size = 1) ++
        MaybeCommentedDecl("Trigger function (controlling recursive postconditions)", triggerFunction(f), size = 1) ++
        MaybeCommentedDecl("State-independent trigger function", triggerFunctionStateless(f), size = 1) ++
        MaybeCommentedDecl("Check contract well-formedness and postcondition", checkFunctionDefinedness(f), size = 1)
      , nLines = 2)

    if (names.isDefined){
      val usedNames = env.currentNameMapping
      // add all local vars
      names.get ++= usedNames
    }

    env = null
    ErrorMemberMapping.currentMember = null
    res
  }

  private def functionDefinitions(f: sil.Function): Seq[Decl] = {
    val typ = translateType(f.typ)
    val fargs = (f.formalArgs map translateLocalVarDecl)
    val args = heapModule.staticStateContributions(true, true) ++ fargs
    val name = Identifier(f.name)
    val func = Func(name, args, typ)
    val name2 = Identifier(f.name + limitedPostfix)
    val func2 = Func(name2, args, typ)
    val funcApp = FuncApp(name, args map (_.l), Bool)
    val funcApp2 = FuncApp(name2, args map (_.l), Bool)
    val triggerFapp = triggerFuncStatelessApp(f , fargs map (_.l))
    val dummyFuncApplication = dummyFuncApp(triggerFapp)
    func ++ func2 ++
      Axiom(Forall(args, Trigger(funcApp), funcApp === funcApp2 && dummyFuncApplication)) ++
      Axiom(Forall(args, Trigger(funcApp2), dummyFuncApplication))
  }

  override def dummyFuncApp(e: Exp): Exp = FuncApp(dummyTriggerName, Seq(e), Bool)

  override def translateFuncApp(fa: sil.FuncApp) = {
    translateFuncApp(fa.funcname, heapModule.currentStateExps ++ (fa.args map translateExp), fa.typ)
  }
  def translateFuncApp(fname : String, args: Seq[Exp], typ: sil.Type) = {
    FuncApp(Identifier(fname), args, translateType(typ))
  }

  private def assumeFunctionsAbove(i: Int): Exp =
    assumeFunctionsAbove < IntLit(i)

  def assumeFunctionsAt(i: Int): Stmt =
    if (verifier.program.functions.isEmpty) Nil
    else Assume(assumeFunctionsAbove === IntLit(i))

  def assumeAllFunctionDefinitions: Stmt = {
    assumeFunctionsAt(-1)
  }

  private def definitionalAxiom(f: sil.Function): Seq[Decl] = {
    val height = heights(f.name)
    val heap = heapModule.staticStateContributions(true, true)
    val args = f.formalArgs map translateLocalVarDecl
    val fapp = translateFuncApp(f.name, (heap ++ args) map (_.l), f.typ)
    val precondition : Exp = f.pres.map(p => translateExp(Expressions.asBooleanExp(p).whenExhaling)) match {
      case Seq() => TrueLit()
      case Seq(p) => p
      case ps => ps.tail.foldLeft(ps.head)((p,q) => BinExp(p,And,q))
    }
    val body = transformFuncAppsToLimitedForm(translateExp(f.body.get),height)

    // The idea here is that we can generate additional triggers for the function definition, which allow its definition to be triggered in any state in which the corresponding *predicate* has been folded or unfolded, in the following scenarios:
    // (a) if the function is recursive, and if the predicate is unfolded around the recursive call in the function body
    // (b) if the function is not recursive, and the predicate is mentioned in its precondition
    // In either case, the function must have been mentioned *somewhere* in the program (not necessarily the state in which its definition is triggered) with the corresponding combination of function arguments.
    val recursiveCallsAndUnfoldings : Seq[(silverFuncApp,Seq[Unfolding])] = Functions.recursiveCallsAndSurroundingUnfoldings(f)
    val outerUnfoldings : Seq[Unfolding] = recursiveCallsAndUnfoldings.map((pair) => pair._2.headOption).flatten

    val predicateTriggers : Seq[Exp] = if (recursiveCallsAndUnfoldings.isEmpty) {
      // then any predicate in the precondition that does not contain bound variables will do (at the moment, regardless of position - seems OK since there is no recursion)
      // (can maybe do something better if bound variables occur)
      val collectDefinedPredicates = (p: sil.Node) =>
        p.shallowCollect {
          case pacc: PredicateAccess => Some(predicateTrigger(heap map (_.l), pacc))
          case quantified: sil.QuantifiedExp => None
          //we might be able to support the Let case, but it's not clear if this is desired
          case let: sil.Let => None
          case forperm: sil.ForPerm => None
        }
      (f.pres.flatMap(p => collectDefinedPredicates(p))).flatten
    } else {
      // since outerUnfoldings may include unfoldings that access predicates using bound variables, we make sure we
      // only include triggers for predicate accesses that do not refer to bound variables (can maybe relax this)
      val silArgsLocalVar = f.formalArgs map (decl => decl.localVar)
      val hasOnlyDefinedVars = (pacc: PredicateAccess) =>
         pacc.args.forall(arg => !arg.existsDefined[Unit]({case v:sil.LocalVar if !silArgsLocalVar.contains(v) => }  ))

      outerUnfoldings.flatMap {
        case Unfolding(PredicateAccessPredicate(predacc: PredicateAccess, perm), exp)
          if hasOnlyDefinedVars(predacc) => Some(predicateTrigger(heap map (_.l), predacc))
        case _ => None}.flatten
    }


    Axiom(Forall(
      stateModule.staticStateContributions() ++ args,
      Seq(Trigger(Seq(staticGoodState,fapp))) ++ (if (predicateTriggers.isEmpty) Seq()  else Seq(Trigger(Seq(staticGoodState, triggerFuncStatelessApp(f,args map (_.l))) ++ predicateTriggers))),
      (staticGoodState && assumeFunctionsAbove(height)) ==>
        (precondition ==> (fapp === body))
    ))
  }

  private def transformFuncAppsToLimitedForm(exp: Exp, heightToSkip : Int = -1): Exp =  transformFuncAppsToLimitedOrTriggerForm(exp, heightToSkip, false)
  /**
   * Transform all function applications to their limited form (or form used in triggers, if the "triggerForm" Boolean is passed as true.
   * If height is provided (i.e., non-negative), functions of above that height need not have their applications replaced with the limited form.
   */
  private def transformFuncAppsToLimitedOrTriggerForm(exp: Exp, heightToSkip : Int = -1, triggerForm: Boolean = false): Exp = {
    def transformer: PartialFunction[Exp, Option[Exp]] = {
      case FuncApp(recf, recargs, t) if recf.namespace == fpNamespace && (heightToSkip == -1 || heights(recf.name) <= heightToSkip) =>
        // change all function applications to use the limited form, and still go through all arguments
        if (triggerForm)
          {val func = verifier.program.findFunction(recf.name)
            // This was an attempt to make triggering functions heap-independent.
            // But the problem is that, for soundness such a function cannot be equated with/substituted for
            // the original function application, and if nested inside further structure in a trigger, the
            // resulting trigger will not be available. e.g. if we had f(Heap,g(Heap,x)) as a trigger, and were to convert
            // it to f#trigger(g#trigger(x)) we wouldn't actually have this term, even given the
            // standard axioms which would add f#trigger(g(x)) and g#trigger(x) to the known terms
            // when a term f(g(x)) was used :
            // Some(triggerFuncApp(func , (recargs.tail map (_.transform(transformer)))))
            //
            // instead, we use the function frame function as the trigger:
            val frameExp : Exp = {
              getFunctionFrame(func, recargs)._1 // the declarations will be taken care of when the function is translated
            }
            Some(FuncApp(Identifier(func.name + framePostfix), Seq(frameExp) ++ (recargs.tail /* drop Heap argument */ map (_.transform(transformer))), t))

          } else Some(FuncApp(Identifier(recf.name + limitedPostfix), recargs map (_.transform(transformer)), t))

      case fa@Forall(vs,ts,e,tvs) => Some(Forall(vs,ts,e.transform(transformer),tvs)) // avoid recursing into the triggers of nested foralls (which will typically get translated via another call to this anyway)
    }
  val res = exp transform transformer
    res
  }

  private def postconditionAxiom(f: sil.Function): Seq[Decl] = {
    val height = heights(f.name)
    val heap = heapModule.staticStateContributions(true, true)
    val args = f.formalArgs map translateLocalVarDecl
    val fapp = translateFuncApp(f.name, (heap ++ args) map (_.l), f.typ)
    val precondition : Exp = f.pres.map(p => translateExp(Expressions.asBooleanExp(p).whenExhaling)) match {
      case Seq() => TrueLit()
      case Seq(p) => p
      case ps => ps.tail.foldLeft(ps.head)((p,q) => BinExp(p,And,q))
    }
    val limitedFapp = transformFuncAppsToLimitedForm(fapp)
    val res = translateResult(sil.Result(f.typ)())
    for (post <- f.posts) yield {
      val translatedPost = translateExp(whenInhaling(post))
      val resultToPrimedFapp : PartialFunction[Exp,Option[Exp]] = {
        case e: LocalVar if e == res => Some(limitedFapp)
      }
      def resultToFapp : PartialFunction[Exp,Option[Exp]] = {
        case e: LocalVar if e == res => Some(fapp)
        case Forall(vs,ts,e,tvs) =>
          Some(Forall(vs,ts map (_ match {case Trigger(trig) => Trigger(trig map (_ transform resultToPrimedFapp)) } ),
            (e transform resultToFapp),tvs))
      }
      val bPost = translatedPost transform resultToFapp
      Axiom(Forall(
        stateModule.staticStateContributions() ++ args,
        Trigger(Seq(staticGoodState, limitedFapp)),
        (staticGoodState && (assumeFunctionsAbove(height) || triggerFuncApp(f,heapModule.staticStateContributions(true,true) map (_.l), args map (_.l)))) ==> (precondition ==> transformFuncAppsToLimitedForm(bPost, height))))
    }
  }

  private def triggerFunction(f: sil.Function): Seq[Decl] = {
    Func(Identifier(f.name + triggerFuncPostfix), LocalVarDecl(Identifier("frame"), frameType) ++ (f.formalArgs map translateLocalVarDecl), Bool)
  }

  private def triggerFuncApp(func: sil.Function, heapArgs: Seq[Exp], normalArgs:Seq[Exp]): Exp = {
    FuncApp(Identifier(func.name + triggerFuncPostfix), getFunctionFrame(func, heapArgs ++ normalArgs)._1 ++ normalArgs, Bool) // no need to declare auxiliary definitions; taken care of in framingAxiom below
  }

  private def triggerFunctionStateless(f: sil.Function): Seq[Decl] = {
    Func(Identifier(f.name + triggerFuncNoHeapPostfix), f.formalArgs map translateLocalVarDecl, translateType(f.typ))
  }

  private def triggerFuncStatelessApp(func: sil.Function, args:Seq[Exp]): Exp = {
    FuncApp(Identifier(func.name + triggerFuncNoHeapPostfix), args, translateType(func.typ))
  }

  private def framingAxiom(f: sil.Function): Seq[Decl] = {
    stateModule.reset()
    val typ = translateType(f.typ)
    val heap = heapModule.staticStateContributions(true, true)
    val realArgs = (f.formalArgs map translateLocalVarDecl)
    val args = heap ++ realArgs
    val name = Identifier(f.name + framePostfix)
    val func = Func(name, LocalVarDecl(Identifier("frame"), frameType) ++ realArgs, typ)
    val funcFrameInfo = getFunctionFrame(f, args map (_.l))
    val funcApp = FuncApp(name, funcFrameInfo._1 ++ (realArgs map (_.l)), typ)
    val funcApp2 = translateFuncApp(f.name, args map (_.l), f.typ)
    val outerUnfoldings : Seq[Unfolding] = Functions.recursiveCallsAndSurroundingUnfoldings(f).map((pair) => pair._2.headOption).flatten

    //only include predicate accesses that do not refer to bound variables
    val silArgsLocalVar = f.formalArgs map (decl => decl.localVar)
    val hasOnlyDefinedVars = (pacc: PredicateAccess) =>
      pacc.args.forall(arg => !arg.existsDefined[Unit]({case v:sil.LocalVar if !silArgsLocalVar.contains(v) => }  ))

    val predicateTriggers : Seq[Exp] = outerUnfoldings.flatMap {
      case Unfolding(PredicateAccessPredicate(predacc: PredicateAccess, perm), exp)
        if hasOnlyDefinedVars(predacc) => Some(predicateTrigger(heap map (_.l), predacc))
      case _ => None}.flatten

    Seq(func) ++
      Seq(Axiom(Forall(
        stateModule.staticStateContributions() ++ realArgs,
        Seq(Trigger(Seq(staticGoodState, transformFuncAppsToLimitedForm(funcApp2)))) ++ (if (predicateTriggers.isEmpty) Seq()  else Seq(Trigger(Seq(staticGoodState, triggerFuncStatelessApp(f,realArgs map (_.l))) ++ predicateTriggers))),
        staticGoodState ==> (transformFuncAppsToLimitedForm(funcApp2) === funcApp))) ) ++
        translateCondAxioms("function "+f.name, f.formalArgs, funcFrameInfo._2)
  }

  /** Generate an expression that represents a snapshot of a predicate's body, representing
    * the heap locations it can depend on.
    *
    * Returns the Boogie expression representing the predicate frame (parameterised with function formal parameters),
    * plus a sequence of information about quantified permissions encountered, which can be used to define functions
    * to define the footprints of the related QPs (when the axioms are generated)
    *
    * The generated frame includes freshly-generated variables
    */
  private def getPredicateFrame(pred: sil.Predicate, args: Seq[Exp]): (Exp, Seq[(Func, sil.Forall)]) = {
    getFrame(pred.name, pred.formalArgs, pred.body.get.whenExhaling, predicateFrames, args, false)
  }


  /** Generate an expression that represents the state a function can depend on
    * (as determined by examining the functions preconditions).
    *
    * Returns the Boogie expression representing the function frame (parameterised with function formal parameters),
    * plus a sequence of information about quantified permissions encountered, which can be used to define functions
    * to define the footprints of the related QPs (when the function axioms are generated)
    *
    * The generated frame includes freshly-generated variables
    */
  private def getFunctionFrame(fun: sil.Function, args: Seq[Exp]): (Exp, Seq[(Func, sil.Forall)]) = {
  val res =     getFrame(fun.name, fun.formalArgs, fun.pres map whenExhaling, functionFrames, args, true)
    res
  }

  /** Generate an expression that represents the state depended on by conjoined assertions,
    * as a "snapshot", used for framing.
    *
    * Returns the Boogie expression representing the  frame (parameterised with provided formal parameters),
    * plus a sequence of information about quantified permissions encountered, which can be used to define functions
    * to define the footprints of the related QPs (when the axioms are generated)
    *
    * The generated frame includes freshly-generated variables
    */
  private def getFrame(name: String, formalArgs:Seq[sil.LocalVarDecl], assertions:Seq[sil.Exp], info: FrameInfos, args: Seq[Exp], argsIncludeHeap : Boolean): (Exp, Seq[(Func, sil.Forall)]) = {
    qpCondFuncs = new ListBuffer[(Func, sil.Forall)]
    (info.get(name) match {
      case Some(frameInfo) => frameInfo
      case None => {
        val (_, state) = stateModule.freshTempState("Frame") // we ignore the initialisation statements, since these variables are just placeholders
        val frameState = stateModule.state
        val freshParamDeclarations = formalArgs map (env.makeUniquelyNamed(_))
        val freshParams = freshParamDeclarations map (_.localVar)
        freshParams map (lv => env.define(lv))
        val freshBoogies = freshParamDeclarations map translateLocalVarDecl
        val renaming = ((e:sil.Exp) => Expressions.instantiateVariables(e,formalArgs,freshParams, env.allDefinedNames(program)))
        val (frame, declarations) = computeFrame(assertions, renaming, name, freshBoogies)
        info.put(name, (frame, frameState, freshBoogies, declarations))
        freshParams map (lv => env.undefine(lv))
        stateModule.replaceState(state) // go back to the original state
        (frame, frameState, freshBoogies, declarations)
      }
    })
    match
    {
      case (frame, frameState, params, declarations) => {
        val frameStateExps = stateContributionValues(frameState)
        val paramVariables = params map (_.l)

        val (heapArgs,normalArgs) =
        if(argsIncludeHeap) {
          val numHeapArgs = heapModule.staticStateContributions(true, true /* second param makes no difference for the HeapModule */).size
          (args take numHeapArgs, args drop numHeapArgs)
        } else {
          (currentStateContributionValues,args)
        }
        val substitution : (Exp => Exp) = _.transform({
          case l@LocalVar(_, _) if (paramVariables.contains(l)) => Some(normalArgs(paramVariables.indexOf(l)))
          case e if (frameStateExps.contains(e)) => Some(heapArgs(frameStateExps.indexOf(e)))
        })
        (substitution(frame), declarations )
      }
    }
  }


  private def computeFrame(conjuncts: Seq[sil.Exp], renaming : sil.Exp => sil.Exp, functionName: String, args:Seq[LocalVarDecl]): (Exp, Seq[(Func, sil.Forall)]) = {
    (conjuncts match {
      case Nil => emptyFrame
      case pre +: Nil => computeFrameHelper(pre,renaming,functionName,args)
      case p +: ps => combineFrames(computeFrameHelper(p,renaming,functionName,args), computeFrame(ps,renaming,functionName,args)._1) // we don't need to return the list, since this is updated statefully
    }, qpCondFuncs)
  }
  private def combineFrames(a: Exp, b: Exp) = {
    if (a.equals(emptyFrame)) b else
    if (b.equals(emptyFrame)) a else
    FuncApp(combineFramesName, Seq(a, b), frameType)
  }
  private def computeFrameHelper(assertion: sil.Exp, renaming: sil.Exp=>sil.Exp, name: String, args:Seq[LocalVarDecl]): Exp = {
    def frameFragment(e: Exp) = {
      FuncApp(frameFragmentName, Seq(e), frameType)
    }
    assertion match {
      case s@sil.AccessPredicate(la, perm) =>
        val fragmentBody = translateLocationAccess(renaming(la).asInstanceOf[sil.LocationAccess])
        val fragment = if (s.isInstanceOf[PredicateAccessPredicate]) fragmentBody else frameFragment(fragmentBody)
        if (permModule.conservativeIsPositivePerm(perm)) fragment else
        FuncApp(condFrameName, Seq(translatePerm(renaming(perm)),fragment),frameType)
      case QuantifiedPermissionAssertion(forall, _, _ : sil.AccessPredicate) => // works the same for fields and predicates
        qpPrecondId = qpPrecondId+1
        val heap = heapModule.staticStateContributions(true, true)
        val condName = Identifier(name + "#condqp" +qpPrecondId.toString)
        val condFunc = Func(condName, heap++args,Int)
        val res = (condFunc, forall)
        qpCondFuncs += res
        frameFragment(FuncApp(condName,heapModule.currentStateExps ++ (args map (_.l)), Int))
      case sil.Implies(e0, e1) =>
        frameFragment(CondExp(translateExp(renaming(e0)), computeFrameHelper(e1,renaming,name,args), emptyFrame))
      case sil.And(e0, e1) =>
        combineFrames(computeFrameHelper(e0,renaming,name,args), computeFrameHelper(e1,renaming,name,args))
      case sil.CondExp(con, thn, els) =>
        frameFragment(CondExp(translateExp(renaming(con)), computeFrameHelper(thn,renaming,name,args), computeFrameHelper(els,renaming,name,args)))
      case sil.Let(varDeclared,boundTo,inBody) =>
        computeFrameHelper(Expressions.instantiateVariables(inBody,varDeclared,boundTo, env.allDefinedNames(program)),renaming,name,args)
      case e if e.isPure =>
        emptyFrame
      // should be no default case! Some explicit cases should be added - e.g. let expressions (see issue 222)
    }
  }

  private def translateCondAxioms(originalName: String, formalArgs: Seq[sil.LocalVarDecl], qps:Seq[(Func,sil.Forall)]): Seq[Decl] =
  {
    val origArgs = formalArgs map translateLocalVarDecl

    (for ((condFunc,qp) <- qps) yield {
      qp match {
        case QuantifiedPermissionAssertion(forall, condition, acc: sil.AccessPredicate) => // same works for field or predicate accesses!
          val lvds = forall.variables // TODO: Generalise to multiple quantified variables
          val perm = acc.perm
          val locationAccess = acc.loc

          val vsFresh = lvds.map(lvd => env.makeUniquelyNamed(lvd))
          vsFresh.foreach(vFresh => env.define(vFresh.localVar))
          def renaming(origExpr: sil.Exp) = Expressions.instantiateVariables(origExpr, lvds, vsFresh.map(_.localVar), env.allDefinedNames(program))


          val (_, curState) = stateModule.freshTempState("Heap2")
          val heap1 = heapModule.currentStateContributions
          val mask1 = permModule.currentStateContributions



          val renamedCond = renaming(if (perm.isInstanceOf[sil.WildcardPerm]) condition else sil.And(condition,PermGtCmp(perm, NoPerm()(forall.pos,forall.info))(forall.pos))(forall.pos,forall.info))



          val locationAccess1 = translateResourceAccess(locationAccess)
          val translatedCond1 = translateExp(renamedCond) //condition just evaluated in one state
          val funApp1 = FuncApp(condFunc.name, (heap1++origArgs) map (_.l), condFunc.typ)


          val (_, _) = stateModule.freshTempState("Heap1")

          val heap2 = heapModule.currentStateContributions
          val mask2 = permModule.currentStateContributions

          val locationAccess2 = translateResourceAccess(locationAccess)
          val translatedCond2 = translateExp(renamedCond)

          val funApp2 = FuncApp(condFunc.name, (heap2++origArgs) map (_.l), condFunc.typ)

          val triggers = if (locationAccess.exists(lvds.toSet)) Seq(Trigger(Seq(locationAccess1,locationAccess2))) else Seq() // TODO: we could (also in general) raise an error/warning if the tools fail to find triggers

          val res = CommentedDecl("Function used for framing of quantified permission " + qp.toString() +  " in " + originalName,
            condFunc ++
            Axiom(
              Forall(heap1 ++ heap2 ++ origArgs, Seq(Trigger(Seq(funApp1, funApp2, heapModule.successorHeapState(heap1,heap2)))),
                  (Forall(vsFresh.map(vFresh => translateLocalVarDecl(vFresh)), triggers,
                    (translatedCond1 <==> translatedCond2) && (translatedCond1 ==> (locationAccess1 === locationAccess2))) ==> (funApp1 === funApp2))
                  ))
          );
          vsFresh.foreach(vFresh => env.undefine(vFresh.localVar))
          stateModule.replaceState(curState)
          res
        case e => sys.error("invalid quantified permission input into method: got " + e)
      }
    }).flatten
  }

  private def checkFunctionDefinedness(f: sil.Function) = {
    checkingDefinednessOfFunction = Some(f.name)
    val args = f.formalArgs map translateLocalVarDecl
    val res = sil.Result(f.typ)()
    val init : Stmt = MaybeCommentBlock("Initializing the state",
      stateModule.initBoogieState ++ (f.formalArgs map (a => allAssumptionsAboutValue(a.typ,mainModule.translateLocalVarDecl(a),true))) ++ assumeFunctionsAt(heights(f.name)))
    val initOld : Stmt = MaybeCommentBlock("Initializing the old state", stateModule.initOldState)
    val checkPre : Stmt = checkFunctionPreconditionDefinedness(f)
    val checkExp : Stmt = if (f.isAbstract) MaybeCommentBlock("(no definition for abstract function)",Nil) else
      MaybeCommentBlock("Check definedness of function body",
      expModule.checkDefinedness(f.body.get, errors.FunctionNotWellformed(f)))
    val exp : Stmt = if (f.isAbstract) MaybeCommentBlock("(no definition for abstract function)",Nil) else
      MaybeCommentBlock("Translate function body",
      translateResult(res) := translateExp(f.body.get))
    val checkPost = checkFunctionPostconditionDefinedness(f)
    val body : Stmt = Seq(init, initOld, checkPre, checkExp, exp, checkPost)
    val definednessChecks = Procedure(Identifier(f.name + "#definedness"), args, translateResultDecl(res), body)
    checkingDefinednessOfFunction = None
    definednessChecks
  }

  private def checkFunctionPostconditionDefinedness(f: sil.Function): Stmt with Product with Serializable = {
    if (contains[sil.InhaleExhaleExp](f.posts)) {
      // Postcondition contains InhaleExhale expression.
      // Need to check inhale and exhale parts separately.
      val onlyInhalePosts: Seq[Stmt] = f.posts map (e => {
        checkDefinednessOfSpecAndInhale(whenInhaling(e), errors.ContractNotWellformed(e))
      })
      val onlyExhalePosts: Seq[Stmt] = if (f.isAbstract) {
        f.posts map (e => {
          checkDefinednessOfSpecAndInhale( // inhale since we are not checking, but want short-circuiting
            whenExhaling(e),
            errors.ContractNotWellformed(e))
        })
      }
      else {
        f.posts map (e => {
          checkDefinednessOfSpecAndExhale(
            whenExhaling(e),
            errors.ContractNotWellformed(e),
            errors.PostconditionViolated(e, f))
        })
      }
      val inhaleCheck = MaybeCommentBlock(
        "Do welldefinedness check of the inhale part.",
        NondetIf(onlyInhalePosts ++ Assume(FalseLit())))
      if (f.isAbstract) {
        MaybeCommentBlock("Checking definedness of postcondition (no body)",
          inhaleCheck ++
          MaybeCommentBlock("Do welldefinedness check of the exhale part.",
            onlyExhalePosts))
      }
      else {
        MaybeCommentBlock("Exhaling postcondition (with checking)",
          inhaleCheck ++
          MaybeCommentBlock("Normally exhale the exhale part.",
            onlyExhalePosts))
      }
    }
    else {
      // Postcondition does not contain InhaleExhale expression.
      if (f.isAbstract) {
        val posts: Seq[Stmt] = f.posts map (e => {
          checkDefinednessOfSpecAndInhale(e, errors.ContractNotWellformed(e)) // inhale since we are not checking, but want short-circuiting
        })
        MaybeCommentBlock("Checking definedness of postcondition (no body)", posts)
      }
      else {
        val posts: Seq[Stmt] = f.posts map (e => {
          checkDefinednessOfSpecAndExhale(
            e,
            errors.ContractNotWellformed(e),
            errors.PostconditionViolated(e, f))
        })
        MaybeCommentBlock("Exhaling postcondition (with checking)", posts)
      }
    }
  }

  private def checkFunctionPreconditionDefinedness(f: sil.Function): Stmt with Product with Serializable = {
    if (contains[sil.InhaleExhaleExp](f.pres)) {
      // Precondition contains InhaleExhale expression.
      // Need to check inhale and exhale parts separately.
      val onlyExhalePres: Seq[Stmt] = checkDefinednessOfExhaleSpecAndInhale(
        f.pres,
        (e) => {
          errors.ContractNotWellformed(e)
        })
      val onlyInhalePres: Seq[Stmt] = checkDefinednessOfInhaleSpecAndInhale(
        f.pres,
        (e) => {
          errors.ContractNotWellformed(e)
        })
      MaybeCommentBlock("Inhaling precondition (with checking)",
        MaybeCommentBlock("Do welldefinedness check of the exhale part.",
          NondetIf(onlyExhalePres ++ Assume(FalseLit()))) ++
          MaybeCommentBlock("Normally inhale the inhale part.",
            onlyInhalePres)
      )
    }
    else {
      val pres: Seq[Stmt] = checkDefinednessOfInhaleSpecAndInhale(
        f.pres,
        (e) => {
          errors.ContractNotWellformed(e)
        })
      MaybeCommentBlock("Inhaling precondition (with checking)", pres)
    }
  }

  private def translateResultDecl(r: sil.Result) = LocalVarDecl(resultName, translateType(r.typ))
  override def translateResult(r: sil.Result) = translateResultDecl(r).l

  private var tmpStateId = -1
  override def partialCheckDefinedness(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean): (() => Stmt, () => Stmt) = {
    e match {
      case u@sil.Unfolding(acc@sil.PredicateAccessPredicate(loc, perm), exp) =>
        tmpStateId += 1
        val tmpStateName = if (tmpStateId == 0) "Unfolding" else s"Unfolding$tmpStateId"
        val (stmt, state) = stateModule.freshTempState(tmpStateName)
        def before() = {
          stmt ++ unfoldPredicate(acc, error, true)
        }
        def after() = {
          tmpStateId -= 1
          stateModule.replaceState(state)
          Nil
        }
        (before _, after _)
      case fa@sil.FuncApp(f, args) => {
        (() => Nil, if(makeChecks) () => {
        val funct = verifier.program.findFunction(f);
        val pres = funct.pres map (e => Expressions.instantiateVariables(e, funct.formalArgs, args, env.allDefinedNames(program)))
        //if (pres.isEmpty) noStmt // even for empty pres, the assumption made below is important
        NondetIf(
          // This is where termination checks could/should be added
          MaybeComment("Exhale precondition of function application", exhale(pres map (e => (e, errors.PreconditionInAppFalse(fa))))) ++
            MaybeComment("Stop execution", Assume(FalseLit()))
          , checkingDefinednessOfFunction match {
            case Some(name) if name.equals(f) => MaybeComment("Enable postcondition for recursive call", Assume(triggerFuncApp(funct,heapModule.currentStateExps,args map translateExp)))
            case _ => Nil
          })} else () => Nil
        )
      }
      case _ => (() => simplePartialCheckDefinedness(e, error, makeChecks), () => Nil)
    }
  }

  override def toExpressionsUsedInTriggers(inputs: Seq[Exp]): Seq[Seq[Exp]] = {
    val res = if (inputs.isEmpty) Seq()
      else if (inputs.size == 1) toExpressionsUsedInTriggers(inputs.head) map (Seq(_))
      else
        for {headResult <- toExpressionsUsedInTriggers(inputs.head); tailResult <- toExpressionsUsedInTriggers(inputs.tail)}
          yield headResult +: tailResult
    res
  }

  override def toExpressionsUsedInTriggers(e: Exp): Seq[Exp] = {
    val inter = transformFuncAppsToLimitedOrTriggerForm(e,-1,true)
    val seqsDone = seqModule.rewriteToTermsInTriggers(inter)
    val res = if (seqsDone != inter)
      (flattenConditionalsInTriggers(seqsDone) ++ flattenConditionalsInTriggers(inter)).distinct
      else flattenConditionalsInTriggers(seqsDone)
    res
  }

  private def flattenConditionalsInTriggers(e: Exp) : Seq[Exp] =
  {
    DuplicatingTransformer.transform(node = e)(post = (_ match {
      case CondExp(cond,thn,els) => Seq(thn,els)
      case n => Seq(n)
    }))
  }

  // --------------------------------------------

  override def translatePredicate(p: sil.Predicate, names: Option[mutable.Map[String, String]]): Seq[Decl] = {

    env = Environment(verifier, p)
    ErrorMemberMapping.currentMember = p
    val args = p.formalArgs
    val translatedArgs = p.formalArgs map translateLocalVarDecl
    val predAcc = sil.PredicateAccess(args map (_.localVar),p)(p.pos,p.info,p.errT)
    val trigger = predicateTrigger(heapModule.staticStateContributions(true, true) map (_.l), predAcc)
    val anystate = predicateTrigger(Seq(), predAcc, true)
    val framingFunctionsToDeclare = if (p.isAbstract) Nil else getPredicateFrame(p,translatedArgs map (_.l))._2 // argument parameters here are just placeholders - we want the auxiliary function definitions.
    val res = MaybeCommentedDecl(s"Translation of predicate ${p.name}",
      predicateGhostFieldDecl(p)) ++
    Axiom(Forall(heapModule.staticStateContributions(true, true) ++ translatedArgs, Seq(Trigger(trigger)), anystate)) ++
      (if (p.isAbstract) Nil else translateCondAxioms("predicate "+p.name, p.formalArgs, framingFunctionsToDeclare))

    val usedNames = env.currentNameMapping

    if (names.isDefined){
      // add all local vars
      names.get ++= usedNames
    }

    env = null
    ErrorMemberMapping.currentMember = null
    res
  }

  override def translateFold(fold: sil.Fold, statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false): (Stmt,Stmt) = {
    fold match {
      case sil.Fold(acc@sil.PredicateAccessPredicate(pa@sil.PredicateAccess(_, _), perm)) => {
        {
          val (foldFirst, foldLast) = foldPredicate(acc, errors.FoldFailed(fold), statesStackForPackageStmt, insidePackageStmt)
          if(insidePackageStmt){
            wandModule.translatingStmtsInWandInit()
          }
          (checkDefinedness(acc, errors.FoldFailed(fold), insidePackageStmt = insidePackageStmt) ++
            checkDefinedness(perm, errors.FoldFailed(fold), insidePackageStmt = insidePackageStmt) ++
            foldFirst, foldLast)
        }
      }
    }
  }

  private var duringFold = false
  private var foldInfo: sil.PredicateAccessPredicate = null
  private def foldPredicate(acc: sil.PredicateAccessPredicate, error: PartialVerificationError
                           , statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false): (Stmt,Stmt) = {
    duringFold = true
    foldInfo = acc
    val stmt = exhale(Seq((Permissions.multiplyExpByPerm(acc.loc.predicateBody(verifier.program, env.allDefinedNames(program)).get,acc.perm), error)), havocHeap = false,
      statesStackForPackageStmt = statesStackForPackageStmt, insidePackageStmt = insidePackageStmt) ++
      inhale(acc, statesStackForPackageStmt, insidePackageStmt)
    val stmtLast =  Assume(predicateTrigger(heapModule.currentStateExps, acc.loc)) ++ {
      val location = acc.loc
      val predicate = verifier.program.findPredicate(location.predicateName)
      val translatedArgs = location.args map (x => translateExpInWand(x))
      Assume(translateLocationAccess(location) === getPredicateFrame(predicate,translatedArgs)._1)
    }

    foldInfo = null
    duringFold = false
    (stmt,stmtLast)
  }

  private var duringUnfold = false
  private var duringUnfolding = false
  private var duringUnfoldingExtraUnfold = false // are we executing an extra unfold, to reflect the meaning of inhaling or exhaling an unfolding expression?
  private var unfoldInfo: sil.PredicateAccessPredicate = null
  override def translateUnfold(unfold: sil.Unfold, statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false): Stmt = {
    unfold match {
      case sil.Unfold(acc@sil.PredicateAccessPredicate(pa@sil.PredicateAccess(_, _), perm)) =>
        checkDefinedness(acc, errors.UnfoldFailed(unfold), insidePackageStmt = insidePackageStmt) ++
          checkDefinedness(perm, errors.UnfoldFailed(unfold)) ++
          unfoldPredicate(acc, errors.UnfoldFailed(unfold), false, statesStackForPackageStmt, insidePackageStmt)
    }
  }

  private def unfoldPredicate(acc: sil.PredicateAccessPredicate, error: PartialVerificationError, isUnfolding: Boolean
                             ,statesStackForPackageStmt: List[Any] = null, insidePackageStmt: Boolean = false, exhaleUnfoldedPredicate : Boolean = true): Stmt = {
    val oldDuringUnfold = duringUnfold
    val oldDuringUnfolding = duringUnfolding
    val oldUnfoldInfo = unfoldInfo
    val oldDuringFold = duringFold
    duringFold = false
    duringUnfold = true
    duringUnfolding = isUnfolding
    unfoldInfo = acc
    val stmt = Assume(predicateTrigger(heapModule.currentStateExps, acc.loc)) ++
      {
        val location = acc.loc
        val predicate = verifier.program.findPredicate(location.predicateName)
        val translatedArgs = location.args map translateExp
        Assume(translateLocationAccess(location) === getPredicateFrame(predicate,translatedArgs)._1)
      } ++
      (if(exhaleUnfoldedPredicate)
          exhale(Seq((acc, error)), havocHeap = false, statesStackForPackageStmt = statesStackForPackageStmt, insidePackageStmt = insidePackageStmt)
      else Nil) ++ inhale(Permissions.multiplyExpByPerm(acc.loc.predicateBody(verifier.program, env.allDefinedNames(program)).get,acc.perm), statesStackForPackageStmt = statesStackForPackageStmt, insidePackageStmt = insidePackageStmt)
    unfoldInfo = oldUnfoldInfo
    duringUnfold = oldDuringUnfold
    duringFold = oldDuringFold
    duringUnfolding = oldDuringUnfolding
    stmt
  }

  override def exhaleExpBeforeAfter(e: sil.Exp, error: PartialVerificationError): (() => Stmt, () => Stmt) = {
    e match {
      case sil.Unfolding(acc, _) => if (duringUnfoldingExtraUnfold) (() => Nil, () => Nil) else // execute the unfolding, since this may gain information
      {
        duringUnfoldingExtraUnfold = true
        tmpStateId += 1
        val tmpStateName = if (tmpStateId == 0) "Unfolding" else s"Unfolding$tmpStateId"
        val (stmt, state) = stateModule.freshTempState(tmpStateName)
        def before() : Stmt = {
          val result = CommentBlock("Execute unfolding (for extra information)",
            // skip removing the predicate instance, since this will have happened earlier in the assertion being exhaled
            // TODO: note that this means that perm expressions for predicates might not behave as expected, this should be investigated
            // see Carbon issue #348
            stmt ++ unfoldPredicate(acc, NullPartialVerificationError, isUnfolding = true, exhaleUnfoldedPredicate = false)
          )
          duringUnfoldingExtraUnfold = false
          result
        }

        def after():Stmt = {
          tmpStateId -= 1
          stateModule.replaceState(state)
          Nil
        }

        (before, after)
      }
      case pap@sil.PredicateAccessPredicate(loc@sil.PredicateAccess(args, predicateName), _) if duringUnfold && currentPhaseId == 0 =>
        val oldVersion = LocalVar(Identifier("oldVersion"), predicateVersionType)
        val newVersion = LocalVar(Identifier("newVersion"), predicateVersionType)
        val curVersion = translateExp(loc)
        val stmt: Stmt = if (exhaleTmpStateId >= 0 || duringUnfolding) Nil else //(oldVersion := curVersion) ++
           Havoc(Seq(newVersion)) ++
              //          Assume(oldVersion < newVersion) ++ // this only made sense with integer versions. In the new model, we even want to allow the possibility of the new version being equal to the old
              (curVersion := newVersion)
        ( () => MaybeCommentBlock("Update version of predicate",
          If(UnExp(Not,hasDirectPerm(loc)), stmt, Nil)), () => Nil)
      case pap@sil.PredicateAccessPredicate(loc@sil.PredicateAccess(_, _), _) if duringFold =>
        ( () => MaybeCommentBlock("Record predicate instance information",
          insidePredicate(foldInfo, pap)), () => Nil)

      case _ => (() => Nil, () => Nil)
    }
  }

  override def predicateVersionType : Type = {
    frameType
  }

  private def insidePredicate(p1: sil.PredicateAccessPredicate, p2: sil.PredicateAccessPredicate): Stmt = {
    Assume(FuncApp(insidePredicateName,Seq(translateLocation(verifier.program.findPredicate(p1.loc.predicateName), p1.loc.args.map(translateExp(_))),translateExp(p1.loc),translateLocation(verifier.program.findPredicate(p2.loc.predicateName), p2.loc.args.map(translateExp(_))),translateExp(p2.loc)),
      Bool))
  }

  var exhaleTmpStateId = -1
  var extraUnfolding = false
  override def inhaleExp(e: sil.Exp): Stmt = {
    e match {
      case sil.Unfolding(acc, _) => if (duringUnfoldingExtraUnfold) Nil else // execute the unfolding, since this may gain information
      {
        duringUnfoldingExtraUnfold = true
        tmpStateId += 1
        val tmpStateName = if (tmpStateId == 0) "Unfolding" else s"Unfolding$tmpStateId"
        val (stmt, state) = stateModule.freshTempState(tmpStateName)
        val stmts = stmt ++ unfoldPredicate(acc, NullPartialVerificationError, true)
        tmpStateId -= 1
        stateModule.replaceState(state)
        duringUnfoldingExtraUnfold = false

        CommentBlock("Execute unfolding (for extra information)",stmts)
      }

      case pap@sil.PredicateAccessPredicate(loc@sil.PredicateAccess(_, _), perm) =>
        val res: Stmt = if (extraUnfolding) {
          exhaleTmpStateId += 1
          extraUnfolding = false
          val tmpStateName = if (exhaleTmpStateId == 0) "ExtraUnfolding" else s"ExtraUnfolding$exhaleTmpStateId"
          val (stmt, state) = stateModule.freshTempState(tmpStateName)
          val r = stmt ++ unfoldPredicate(pap, NullPartialVerificationError, true)
          extraUnfolding = true
          exhaleTmpStateId -= 1
          stateModule.replaceState(state)
          r
        } else Nil
        MaybeCommentBlock("Extra unfolding of predicate",
          res ++ (if (duringUnfold) insidePredicate(unfoldInfo, pap) else Nil))
      case _ => Nil
    }
  }
}
