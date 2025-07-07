// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

package viper.carbon.modules.impls

import viper.carbon.boogie.{Bool, CondExp, Exp, FalseLit, Forall, If, Int, IntLit, LocalVar, LocalVarDecl, MaybeCommentBlock, Stmt, Trigger, TypeVar, _}
import viper.carbon.modules._
import viper.silver.ast.{FuncApp => silverFuncApp}
import viper.silver.ast.utility.Expressions.{contains, whenExhaling, whenInhaling}
import viper.silver.ast.{NoPerm, PermGtCmp, PredicateAccess, PredicateAccessPredicate, Unfolding}
import viper.silver.{ast => sil}
import viper.carbon.verifier.{Environment, Verifier}
import viper.carbon.boogie.Implicits._
import viper.silver.ast.utility._
import viper.carbon.modules.components.{DefinednessComponent, DefinednessState, ExhaleComponent, InhaleComponent}
import viper.silver.verifier.{NullPartialVerificationError, PartialVerificationError, errors}

import scala.collection.mutable.ListBuffer
import viper.silver.ast.utility.QuantifiedPermissions.QuantifiedPermissionAssertion
import viper.silver.verifier.reasons.NonPositivePermission

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

  /* limitedPostfix is appended to the actual function name to get the name of the limited function.
   * It must be a string that cannot appear in Viper identifiers to ensure that we can easily check if a given identifier
   * refers to the limited version of a function or not.
   */
  private val limitedPostfix = "'"
  private val triggerFuncPostfix = "#trigger"
  private val triggerFuncNoHeapPostfix = "#triggerStateless"
  private val framePostfix = "#frame"
  private val frameTypeName = "FrameType"
  private val frameType = NamedType(frameTypeName)
  private val emptyFrameName = Identifier("EmptyFrame")
  private val emptyFrame = Const(emptyFrameName)
  private val combineFramesName = Identifier("CombineFrames")
  private val frameFirstName = Identifier("FrameFirst")
  private val frameSecondName = Identifier("FrameSecond")
  private val frameFragmentName = Identifier("FrameFragment")
  private val frameContentName = Identifier("FrameContent")
  private val condFrameName = Identifier("ConditionalFrame")
  private val dummyTriggerName = Identifier("dummyFunction")
  private val resultName = Identifier("Result")
  private val insidePredicateName = Identifier("InsidePredicate")

  private val qpCondPostfix = "#condqp"
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
          Func(frameContentName, Seq(LocalVarDecl(Identifier("f"), frameType)), TypeVar("T")) ++
          Func(condFrameName, Seq(LocalVarDecl(Identifier("p"), permType), LocalVarDecl(Identifier("f"), frameType)), frameType) ++
          Func(dummyTriggerName, Seq(LocalVarDecl(Identifier("t"), TypeVar("T"))), Bool) ++
          Func(frameFirstName, Seq(LocalVarDecl(Identifier("f"), frameType)), frameType) ++
          Func(frameSecondName, Seq(LocalVarDecl(Identifier("f"), frameType)), frameType) ++
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
      CommentedDecl("Inverse function definitions for frame functions",
        {
          val t = LocalVarDecl(Identifier("t"), TypeVar("T"))
          val frameContentInverseAxiom = Axiom(Forall(Seq(t), Trigger(FuncApp(frameFragmentName, Seq(t.l), frameType)),
            FuncApp(frameContentName, Seq(FuncApp(frameFragmentName, Seq(t.l), frameType)), frameType) === t.l))
          val f1 = LocalVarDecl(Identifier("f1"), frameType)
          val f2 = LocalVarDecl(Identifier("f2"), frameType)
          val combined = FuncApp(combineFramesName, Seq(f1.l, f2.l), frameType)
          val frameCombineInverseAxiom = Axiom(Forall(Seq(f1, f2), Trigger(combined),
            FuncApp(frameFirstName, Seq(combined), frameType) === f1.l &&
              FuncApp(frameSecondName, Seq(combined), frameType) === f2.l))
          Seq(frameContentInverseAxiom, frameCombineInverseAxiom)
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

  override def start(): Unit = {
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

    val oldCheckReadPermOnly = permModule.setCheckReadPermissionOnly(!verifier.respectFunctionPrecPermAmounts)
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

    permModule.setCheckReadPermissionOnly(oldCheckReadPermOnly)
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
    val forceNonLimited = fa.info.getUniqueInfo[sil.AnnotationInfo] match {
      case Some(ai) if ai.values.contains("reveal") => true
      case _ => false
    }
    translateFuncApp(fa.funcname, heapModule.currentStateExps ++ (fa.args map translateExp), fa.typ, forceNonLimited)
  }

  def translateFuncApp(fname : String, args: Seq[Exp], typ: sil.Type, forceNonLimited: Boolean) = {
    val func = verifier.program.findFunction(fname)
    val useLimited = !forceNonLimited && (func.info.getUniqueInfo[sil.AnnotationInfo] match {
      case Some(ai) if ai.values.contains("opaque") => true
      case _ => false
    })
    val ident = if (useLimited) Identifier(fname + limitedPostfix) else Identifier(fname)
    FuncApp(ident, args, translateType(typ))
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
    val fapp = translateFuncApp(f.name, (heap ++ args) map (_.l), f.typ, true)
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
          case _: sil.QuantifiedExp => None
          //we might be able to support the Let case, but it's not clear if this is desired
          case _: sil.Let => None
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

    // Do not use predicate triggers if the function is annotated as opaque
    val usePredicateTriggers = f.info.getUniqueInfo[sil.AnnotationInfo] match {
      case Some(ai) if ai.values.contains("opaque") => false
      case _ => true
    }

    Axiom(Forall(
      stateModule.staticStateContributions() ++ args,
      Seq(Trigger(Seq(staticGoodState,fapp))) ++ (if (!usePredicateTriggers || predicateTriggers.isEmpty) Seq()  else Seq(Trigger(Seq(staticGoodState, triggerFuncStatelessApp(f,args map (_.l))) ++ predicateTriggers))),
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
      case FuncApp(recf, recargs, t) if recf.namespace == fpNamespace &&
        // recf might refer to a limited function already if the function was marked as opaque.
        // In that case, we have to drop the limited postfix, since heights contains only the original function names.
        // We assume that any name that ends with limitedPostfix refers to a limited function (see limitedPostfix above).
        (heightToSkip == -1 || heights(if (recf.name.endsWith(limitedPostfix)) recf.name.dropRight(limitedPostfix.length) else recf.name) <= heightToSkip) =>

        val baseName = if (recf.name.endsWith(limitedPostfix)) recf.name.dropRight(limitedPostfix.length) else recf.name
        // change all function applications to use the limited form, and still go through all arguments
        if (triggerForm)
          {val func = verifier.program.findFunction(baseName)
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
            Some(FuncApp(Identifier(baseName + framePostfix), Seq(frameExp) ++ (recargs.tail /* drop Heap argument */ map (_.transform(transformer))), t))

          } else Some(FuncApp(Identifier(baseName + limitedPostfix), recargs map (_.transform(transformer)), t))

      case Forall(vs,ts,e,tvs,w) => Some(Forall(vs,ts,e.transform(transformer),tvs,w)) // avoid recursing into the triggers of nested foralls (which will typically get translated via another call to this anyway)
      case Exists(vs,ts,e,w) => Some(Exists(vs,ts,e.transform(transformer),w)) // avoid recursing into the triggers of nested exists (which will typically get translated via another call to this anyway)
    }
  val res = exp transform transformer
    res
  }

  private def postconditionAxiom(f: sil.Function): Seq[Decl] = {
    val height = heights(f.name)
    val heap = heapModule.staticStateContributions(true, true)
    val args = f.formalArgs map translateLocalVarDecl
    val fapp = translateFuncApp(f.name, (heap ++ args) map (_.l), f.typ, true)
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
        case Forall(vs,ts,e,tvs,w) =>
          Some(Forall(vs,ts map (_ match {case Trigger(trig) => Trigger(trig map (_ transform resultToPrimedFapp)) } ),
            (e transform resultToFapp),tvs,w))
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
    val funcApp2 = translateFuncApp(f.name, args map (_.l), f.typ, true)
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
    }, qpCondFuncs.toSeq)
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
        val fragmentBody = translateResourceAccess(renaming(la).asInstanceOf[sil.LocationAccess])
        val fragment = if (s.isInstanceOf[PredicateAccessPredicate]) fragmentBody else frameFragment(fragmentBody)
        if (permModule.conservativeIsPositivePerm(perm)) fragment else
        FuncApp(condFrameName, Seq(translatePerm(renaming(perm)),fragment),frameType)
      case QuantifiedPermissionAssertion(forall, _, _ : sil.AccessPredicate) => // works the same for fields and predicates
        qpPrecondId = qpPrecondId+1
        val heap = heapModule.staticStateContributions(true, true)
        val condName = Identifier(name + qpCondPostfix + qpPrecondId.toString)
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

          // Pair each quantified variable with a Skolem function on condFunc applications (rather than all condFunc params)
          // This shares witness variables for term equalities, resulting in fewer evaluated heap accesses in framing proofs
          val lvsToSkFunctions: Seq[(LocalVar, Func)] = vsFresh.map(vFresh => {
            val lvd = translateLocalVarDecl(vFresh)
            (lvd.l,
            Func(Identifier(env.uniqueName("sk_" + condFunc.name.name)),
              Seq(LocalVarDecl(Identifier(env.uniqueName("fnAppH1")), condFunc.typ),
                  LocalVarDecl(Identifier(env.uniqueName("fnAppH2")), condFunc.typ)),
              lvd.typ))
          })
          val skSubs = lvsToSkFunctions.map(lvSkPair =>
            (lvSkPair._1, FuncApp(lvSkPair._2.name, Seq(funApp1, funApp2), lvSkPair._2.typ)))

          // Replace quantified index variables with Skolem functions in extensional equality on heap locations
          val extEq = (translatedCond1 <==> translatedCond2) && (translatedCond1 ==> (locationAccess1 === locationAccess2))
          val skExtEq = skSubs.foldLeft(extEq)((body, skSub) => body.replace(skSub._1, skSub._2))

          val res = CommentedDecl("Function used for framing of quantified permission " + qp.toString +  " in " + originalName,
            condFunc ++
              lvsToSkFunctions.map(_._2) ++
              Axiom(
                Forall(
                  heap1 ++ heap2 ++ origArgs,
                  Seq(Trigger(Seq(funApp1, funApp2, heapModule.successorHeapState(heap1,heap2)))),
                  skExtEq ==> (funApp1 === funApp2)
                )
              )
          )

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
      stateModule.initBoogieState ++ (if (verifier.respectFunctionPrecPermAmounts) Nil else permModule.assumePermUpperBounds(false)) ++
        (f.formalArgs map (a => allAssumptionsAboutValue(a.typ,mainModule.translateLocalVarDecl(a),true))) ++ assumeFunctionsAt(heights(f.name)))
    val checkPre : Stmt = checkFunctionPreconditionDefinedness(f)
    val checkExp : Stmt = if (f.isAbstract) MaybeCommentBlock("(no definition for abstract function)",Nil) else
      MaybeCommentBlock("Check definedness of function body",
      expModule.checkDefinedness(f.body.get, errors.FunctionNotWellformed(f)))
    val exp : Stmt = if (f.isAbstract) MaybeCommentBlock("(no definition for abstract function)",Nil) else
      MaybeCommentBlock("Translate function body",
      translateResult(res) := translateExp(f.body.get))
    val checkPost = checkFunctionPostconditionDefinedness(f)
    val body : Stmt = Seq(init, checkPre, checkExp, exp, checkPost)
    val definednessChecks = Procedure(Identifier(f.name + "#definedness"), args, translateResultDecl(res), body)
    checkingDefinednessOfFunction = None
    definednessChecks
  }

  /** check that body of predicate is self-framing */
  private def checkPredicateDefinedness(p: sil.Predicate) : Option[Procedure] = {
    if(p.isAbstract) {
      return None
    }

    val args = p.formalArgs map translateLocalVarDecl
    val init : Stmt = MaybeCommentBlock("Initializing the state",
      stateModule.initBoogieState ++ assumeAllFunctionDefinitions ++
        (if (verifier.respectFunctionPrecPermAmounts) Nil else permModule.assumePermUpperBounds(true)) ++
        (p.formalArgs map (a => allAssumptionsAboutValue(a.typ,mainModule.translateLocalVarDecl(a),true)))
    )

    val predicateBody = p.body.get
    val procedureBody =
      MaybeCommentBlock("Check definedness of predicate body of " + p.name, init ++ inhaleWithDefinednessCheck(predicateBody, errors.PredicateNotWellformed(p)))
    val predicateCheck = Procedure(Identifier(p.name  + "#definedness"), args, Seq(), procedureBody)

    Some(predicateCheck)
  }

  private def checkFunctionPostconditionDefinedness(f: sil.Function): Stmt with Product with Serializable = {
    if (contains[sil.InhaleExhaleExp](f.posts)) {
      // Postcondition contains InhaleExhale expression.
      // Need to check inhale and exhale parts separately.
      val onlyInhalePosts: Seq[Stmt] = f.posts map (e => {
        inhaleWithDefinednessCheck(whenInhaling(e), errors.ContractNotWellformed(e))
      })
      val onlyExhalePosts: Seq[Stmt] = if (f.isAbstract) {
        f.posts map (e => {
          inhaleWithDefinednessCheck( // inhale since we are not checking, but want short-circuiting
            whenExhaling(e),
            errors.ContractNotWellformed(e))
        })
      }
      else {
          exhale(
            f.posts map (e => {
              (
                whenExhaling(e),
                errors.PostconditionViolated(e, f),
                Some(errors.ContractNotWellformed(e))
              )
            })
          )
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
          inhaleWithDefinednessCheck(e, errors.ContractNotWellformed(e)) // inhale since we are not checking, but want short-circuiting
        })
        MaybeCommentBlock("Checking definedness of postcondition (no body)", posts)
      }
      else {
        val posts: Seq[Stmt] =
            exhale(
              f.posts map (e => {
                (
                  e,
                  errors.PostconditionViolated(e, f),
                  Some(errors.ContractNotWellformed(e))
                )
              })
            )
        MaybeCommentBlock("Exhaling postcondition (with checking)", posts)
      }
    }
  }

  private def checkFunctionPreconditionDefinedness(f: sil.Function): Stmt with Product with Serializable = {
    if (contains[sil.InhaleExhaleExp](f.pres)) {
      // Precondition contains InhaleExhale expression.
      // Need to check inhale and exhale parts separately.
      val onlyExhalePres: Seq[Stmt] = inhaleExhaleSpecWithDefinednessCheck(
        f.pres,
        (e) => {
          errors.ContractNotWellformed(e)
        })
      val onlyInhalePres: Seq[Stmt] = inhaleInhaleSpecWithDefinednessCheck(
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
      val pres: Seq[Stmt] = inhaleInhaleSpecWithDefinednessCheck(
        f.pres,
        (e) => {
          errors.ContractNotWellformed(e)
        })
      MaybeCommentBlock("Inhaling precondition (with checking)", pres)
    }
  }

  private def translateResultDecl(r: sil.Result) = LocalVarDecl(resultName, translateType(r.typ))
  override def translateResult(r: sil.Result) = translateResultDecl(r).l

  /***
    * Emits the statement for unfolding into the previous definedness state and adjusts the definedness state.
    * This is achieved by creating a new definedness state that is initialized to the previous definedness state.
    * As a result, there is a side-effect to @{code defState}. The method returns a function to revert the side-effect.
    * @param predAcc
    * @param error
    * @param defState definedness state --> method has a side-effect on this
    * @param tmpUnfoldStateName name of new definedness state
    * @return a tuple with two values, where:
    *         element 1: the statement for the unfolding operation
    *         element 2: a function to revert the side-effect on @{code defState}
    */
  private def unfoldingIntoDefinednessState(predAcc: sil.PredicateAccessPredicate, error: PartialVerificationError,
                                            defState: DefinednessState, tmpUnfoldStateName: String): (Stmt, () => Unit) = {
    val prevMainState = stateModule.state
    val setDefStateBeforeUnfolding = defState.setDefState

    //set the def state before the unfolding operation
    setDefStateBeforeUnfolding()

    //create def state after the unfolding operation and set current state to this state
    val (initStmt, _) = stateModule.freshTempState(tmpUnfoldStateName)
    val defStateAfterUnfolding = stateModule.state

    //unfold into this new state
    val unfoldStmt = unfoldPredicate(predAcc, error, true)

    /** FIXME:
      * Here we are doing the entire predicate unfolding in the definedness state. This means that expressions that
      * are part of the unfolding (e.g., predicate arguments) are evaluated in the definedness state instead of the
      * evaluation state (i.e., the main state before the unfolding). This can lead to discrepancies if the expressions
      * contain permission introspection.
      */

    //set new definedness state
    defState.setDefState = () => stateModule.replaceState(defStateAfterUnfolding)

    //go back to main state before unfolding
    stateModule.replaceState(prevMainState)

    (initStmt ++ unfoldStmt, () => defState.setDefState = setDefStateBeforeUnfolding)
  }

  private var tmpStateId = -1
  override def partialCheckDefinedness(e: sil.Exp, error: PartialVerificationError, makeChecks: Boolean, definednessStateOpt: Option[DefinednessState]): (() => Stmt, () => Stmt) = {
    e match {
      case sil.Unfolding(acc@sil.PredicateAccessPredicate(_, _), _) =>
        tmpStateId += 1
        val tmpStateName = if (tmpStateId == 0) "Unfolding" else s"Unfolding$tmpStateId"

        /** If there is a definedness state d, then we create a new definedness state during the unfolding operation,
          * which is the result of applying the unfold operation in d. The current state is not changed in this case.
          *
          * If there is no definedness state, then we create a new state n that is the result of applying the unfold
          * operation in the current state. The current state is then switched to n during the unfolding. */

        val (unfoldStmt : Stmt, restoreState) =
          definednessStateOpt match {
            case Some(defState) =>
              //Note: the following statement has a side-effect on the definedness state, which is then reverted via @{code restoreState}
              unfoldingIntoDefinednessState(acc, error, defState, tmpStateName)
            case None =>
              val (initStmt, prevState) = stateModule.freshTempState(tmpStateName)
              val unfoldStmt = unfoldPredicate(acc, error, true)
              ((initStmt ++ unfoldStmt) : Stmt, () => stateModule.replaceState(prevState))
          }

        def before() = {
          unfoldStmt
        }
        def after() = {
          tmpStateId -= 1
          restoreState()
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
          MaybeComment("Exhale precondition of function application", {
              val executeExhale = () => exhaleWithoutDefinedness(pres map (e => (e, errors.PreconditionInAppFalse(fa))))

              definednessStateOpt match {
                case Some(defState) =>
                  //need to exhale precondition in the definedness state
                  /** FIXME:
                    * Here we are doing the entire precondition exhale in the definedness state. This means that expressions that
                    * are part of the function call (e.g., function arguments) are evaluated in the definedness state instead of the
                    * evaluation state (i.e., the main state before the function call). This can lead to discrepancies if the expressions
                    * contain permission introspection.
                    */
                  val curState = stateModule.state
                  val oldCheckReadPermOnly = permModule.setCheckReadPermissionOnly(!verifier.respectFunctionPrecPermAmounts)
                  defState.setDefState()
                  val res = executeExhale()
                  permModule.setCheckReadPermissionOnly(oldCheckReadPermOnly)
                  stateModule.replaceState(curState)
                  res
                case None =>
                  val oldCheckReadPermOnly = permModule.setCheckReadPermissionOnly(!verifier.respectFunctionPrecPermAmounts)
                  val res = executeExhale()
                  permModule.setCheckReadPermissionOnly(oldCheckReadPermOnly)
                  res
              }
            }
          ) ++
            MaybeComment("Stop execution", Assume(FalseLit()))
          , checkingDefinednessOfFunction match {
            case Some(name) if name.equals(f) => MaybeComment("Enable postcondition for recursive call", Assume(triggerFuncApp(funct,heapModule.currentStateExps,args map translateExp)))
            case _ => Nil
          })} else () => Nil
        )
      }
      case _ =>
        (
          () => simplePartialCheckDefinednessBefore(e, error, makeChecks, definednessStateOpt),
          () => simplePartialCheckDefinednessAfter(e, error, makeChecks, definednessStateOpt)
        )
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
      (if (p.isAbstract) Nil else
        translateCondAxioms("predicate "+p.name, p.formalArgs, framingFunctionsToDeclare))  ++
      checkPredicateDefinedness(p)

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
            // If no permission amount is supplied explicitly, we always use the default FullPerm; this is
            // okay even if we are inside a function and only want to check for some positive amount, because permission
            // amounts do not matter in this context.
            checkDefinedness(perm.getOrElse(sil.FullPerm()()), errors.FoldFailed(fold), insidePackageStmt = insidePackageStmt) ++
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
    val stmt = Assert(permModule.isStrictlyPositivePerm(acc.perm), error.dueTo(NonPositivePermission(acc.perm))) ++
      exhaleSingleWithoutDefinedness(Permissions.multiplyExpByPerm(acc.loc.predicateBody(verifier.program, env.allDefinedNames(program)).get,acc.perm), error, havocHeap = false,
      statesStackForPackageStmt = statesStackForPackageStmt, insidePackageStmt = insidePackageStmt) ++
      inhale(Seq((acc, error)), addDefinednessChecks = false, statesStackForPackageStmt, insidePackageStmt)
    val stmtLast =  Assume(predicateTrigger(heapModule.currentStateExps, acc.loc)) ++ {
      val location = acc.loc
      val predicate = verifier.program.findPredicate(location.predicateName)
      val translatedArgs = location.args map (x => translateExpInWand(x))
      Assume(translateResourceAccess(location) === getPredicateFrame(predicate,translatedArgs)._1)
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
          // If no permission amount is supplied explicitly, we always use the default FullPerm; this is
          // okay even if we are inside a function and only want to check for some positive amount, because permission
          // amounts do not matter in this context.
          checkDefinedness(perm.getOrElse(sil.FullPerm()()), errors.UnfoldFailed(unfold)) ++
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
    val stmt = Assert(permModule.isStrictlyPositivePerm(acc.perm), error.dueTo(NonPositivePermission(acc.perm))) ++
      Assume(predicateTrigger(heapModule.currentStateExps, acc.loc)) ++
      {
        val location = acc.loc
        val predicate = verifier.program.findPredicate(location.predicateName)
        val translatedArgs = location.args map translateExp
        Assume(translateResourceAccess(location) === getPredicateFrame(predicate,translatedArgs)._1)
      } ++
      (if(exhaleUnfoldedPredicate)
          exhaleSingleWithoutDefinedness(acc, error, havocHeap = false, statesStackForPackageStmt = statesStackForPackageStmt, insidePackageStmt = insidePackageStmt)
      else Nil) ++ inhale(Seq((Permissions.multiplyExpByPerm(acc.loc.predicateBody(verifier.program, env.allDefinedNames(program)).get,acc.perm), error)), addDefinednessChecks = false, statesStackForPackageStmt = statesStackForPackageStmt, insidePackageStmt = insidePackageStmt)
    unfoldInfo = oldUnfoldInfo
    duringUnfold = oldDuringUnfold
    duringFold = oldDuringFold
    duringUnfolding = oldDuringUnfolding
    stmt
  }

  override def exhaleExpBeforeAfter(e: sil.Exp, error: PartialVerificationError, definednessStateOpt: Option[DefinednessState]): (() => Stmt, () => Stmt) = {
    e match {

      case sil.Unfolding(acc, _) =>
        if (definednessStateOpt.isEmpty || duringUnfoldingExtraUnfold) {
          /* If we do not have a definedness state, then we do not perform an unfolding operation to gain more information,
             because the unfolding operation can only be safely performed in the definedness state.
             Also, if we are already performing an unfolding operation to gain more information, then we choose not go gain more information.
           */
          (() => Nil, () => Nil)
        } else {
          /* Execute the unfolding, since we need to update the definedness state (as specified by the interface) and
           * since this may gain information.
           *
           * Note that executing the unfolding in the current evaluation state (instead of in the definedness state)
           * instead is not safe in general:
           * In the current evaluation state, the to-be-unfolded predicate may (or may not) have already been exhaled so
           * it is not clear how to execute the unfolding. In a previous version, the unfolding operation was executed
           * in the current evaluation state by inhaling permission to the predicate's body without removing any permission
           * to the predicate itself. This led to cases where one assumed "state(heap,mask)" in cases where the mask had
           * too much permission due to an unfolded predicate not being removed (this may not be an issue, but arguing
           * why it is not an issue is much more subtle than the current approach). */

          duringUnfoldingExtraUnfold = true
          tmpStateId += 1
          val tmpStateName = if (tmpStateId == 0) "Unfolding" else s"Unfolding$tmpStateId"
          /** Note: the following statement has a side-effect on the definedness state, which is then reverted via @{code restoreState}
            * Also note that there should always be sufficient permission to the unfolded predicate because there must have been
            * a definedness check that asserts it before (in the same state).
            * Nevertheless, we do the check again here to make sure there is no mismatch with the definedness check
            * (to omit the check, we could pass in a [[NullPartialVerificationError]]).
            */
          val (unfoldStmt : Stmt, restoreState) = unfoldingIntoDefinednessState(acc, error, definednessStateOpt.get, tmpStateName)
          duringUnfoldingExtraUnfold = false

          def before() : Stmt = {
            val result = CommentBlock("Execute unfolding (for extra information)",
              /* TODO: Permission introspection is not affected by unfolding operations here. It has not been decided
                       how to treat permission introspection within unfolding operations (see Silver issue #682).  */
              unfoldStmt
            )
            stateModule.replaceState(state)
            result
          }

          def after() : Stmt = {
            tmpStateId -= 1
            restoreState()
            Nil
          }

          (before, after)
      }
      case pap@sil.PredicateAccessPredicate(loc@sil.PredicateAccess(args, predicateName), _) if duringUnfold =>
        val oldVersion = LocalVar(Identifier("oldVersion"), predicateVersionType)
        val newVersion = LocalVar(Identifier("newVersion"), predicateVersionType)
        val stmt: Stmt = if (exhaleTmpStateId >= 0 || duringUnfolding) Nil else //(oldVersion := curVersion) ++
           Havoc(Seq(newVersion)) ++
              //          Assume(oldVersion < newVersion) ++ // this only made sense with integer versions. In the new model, we even want to allow the possibility of the new version being equal to the old
              currentHeapAssignUpdate(loc, newVersion)
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
  override def inhaleExp(e: sil.Exp, error: PartialVerificationError): Stmt = {
    e match {
      case sil.Unfolding(acc, _) =>
        if (duringUnfoldingExtraUnfold) {
          Nil
        } else {
        // execute the unfolding, since this may gain information
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

  def translateBackendFuncApp(fa: sil.BackendFuncApp): Exp = {
    // Do not use funcpred namespace, see translateSMTFunc.
    val funcIdent = Identifier(fa.backendFuncName)(silVarNamespace)
    val res = FuncApp(funcIdent, fa.args map translateExp, translateType(fa.typ))
    res.showReturnType = true
    res
  }

  def translateBackendFunc(f: sil.DomainFunc): Seq[Decl] = {
    // We do not use the funcpred namespace because based on the namespace, the funcpred module
    // decides whether to stuff meant only for heap-dependent functions (like heights computation
    // and limited functions).
    val funcIdent=Identifier(f.name)(silVarNamespace)
    env = Environment(verifier, f)
    val t = translateType(f.typ)
    val args = f.formalArgs map (x => LocalVarDecl(Identifier(if (x.isInstanceOf[sil.LocalVarDecl]) x.asInstanceOf[sil.LocalVarDecl].name else env.uniqueName(f.name + "_param")), translateType(x.typ)))
    var attributes: Map[String, String] = Map()
    attributes += "builtin" -> f.interpretation.get
    val func = Func(funcIdent, args, t, attributes)
    val res = MaybeCommentedDecl(s"Translation of SMT function ${f.name}", func, size = 1)
    env = null
    res
  }
}
