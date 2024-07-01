package viper.carbon.boogie

import scala.collection.mutable
import scala.collection.immutable._
import viper.carbon.verifier.FailureContextImpl
import viper.silver.verifier._
import viper.silver.ast
import viper.silver.ast.{Field, MagicWand, Member, Predicate, Resource}
import viper.silver.verifier.{AbstractError, ApplicationEntry, ConstantEntry, MapEntry, Model, ModelEntry, SimpleCounterexample, UnspecifiedEntry, ValueEntry, VerificationError}
import viper.silver.ast.{Declaration, MagicWandStructure, Program, Type}

/**
  * Transforms a counterexample returned by Boogie back to a Viper counterexample. The programmer can choose between an
  * "intermediate" CE or an "extended" CE.
  */

/**
  * CounterexampleGenerator class used for generating an "extended" CE.
  */
case class CounterexampleGenerator(e: AbstractError, names: Map[String, Map[String, String]], program: Program, wandNames: Option[Map[MagicWandStructure.MagicWandStructure, Func]]) extends Counterexample {
  val ve = e.asInstanceOf[VerificationError]
  val errorMethod = ErrorMemberMapping.mapping.get(ve.readableMessage(true, true)).get
  val imCE = IntermediateCounterexampleModel(ve, errorMethod, names, program, wandNames)
  val model = imCE.originalEntries
  //println(model)

  val (ceStore, refOcc) = CounterexampleGenerator.detStore(program.methodsByName.get(errorMethod.name).get.transitiveScopedDecls, imCE.basicVariables, imCE.allCollections)
  val nameTranslationMap = CounterexampleGenerator.detTranslationMap(ceStore, refOcc)
  var ceHeaps = imCE.allBasicHeaps.map(bh => (bh._1, CounterexampleGenerator.detHeap(imCE.workingModel, bh._2, program, imCE.allCollections, nameTranslationMap, imCE.originalEntries))).reverse

  val domainsAndFunctions = CounterexampleGenerator.detTranslatedDomains(imCE.DomainEntries, nameTranslationMap) ++ CounterexampleGenerator.detTranslatedFunctions(imCE.nonDomainFunctions, nameTranslationMap)

  override def toString: String = {
    var finalString = "      Extended Counterexample: \n"
    finalString += "   Store: \n"
    if (!ceStore.storeEntries.isEmpty)
      finalString += ceStore.storeEntries.map(x => x.toString).mkString("", "\n", "\n")
    if (!ceHeaps.filter(y => !y._2.heapEntries.isEmpty).isEmpty)
      finalString += ceHeaps.filter(y => !y._2.heapEntries.isEmpty).map(x => "   " + x._1 + " Heap: \n" + x._2.toString).mkString("")
    if (domainsAndFunctions.nonEmpty) {
      finalString += "   Domains: \n"
      finalString += domainsAndFunctions.map(x => x.toString).mkString("", "\n", "\n")
    }
    finalString
  }
}

/**
  * CounterexampleGenerator class used for generating an "interemediate" CE.
  */
case class IntermediateCounterexampleModel(ve: VerificationError, errorMethod: Member, names: Map[String, Map[String, String]], program: Program, wandNames: Option[Map[MagicWandStructure.MagicWandStructure, Func]]) extends Counterexample {
  val originalEntries = ve.failureContexts(0).counterExample.get.model
  val model = originalEntries
  val typenamesInMethod = names.get(errorMethod.name).get.map(e => e._2 -> e._1)
  val methodVarDecl = program.methodsByName.get(errorMethod.name).get.transitiveScopedDecls

  val (basicVariables, otherDeclarations) = IntermediateCounterexampleModel.detCEvariables(originalEntries.entries, typenamesInMethod, methodVarDecl)
  val allSequences = IntermediateCounterexampleModel.detSequences(originalEntries)
  val allSets = IntermediateCounterexampleModel.detSets(originalEntries)
  val allMultisets = IntermediateCounterexampleModel.detMultisets(originalEntries)
  val allCollections = allSequences ++ allSets ++ allMultisets

  val workingModel = IntermediateCounterexampleModel.buildNewModel(originalEntries.entries)
  val (hmLabels, hmStates) = IntermediateCounterexampleModel.oldAndReturnHeapMask(workingModel, otherDeclarations)
  val allBasicHeaps = IntermediateCounterexampleModel.detHeaps(workingModel, hmStates, originalEntries, hmLabels, program).map{case (n, bh) => if (n == "return") ("current", bh) else (n, bh)}

  val DomainEntries = IntermediateCounterexampleModel.getAllDomains(originalEntries, program)
  val nonDomainFunctions = IntermediateCounterexampleModel.getAllFunctions(originalEntries, program, hmStates)

  override def toString: String = {
    var finalString = "      Intermediate Counterexample: \n"
    finalString ++= "   Local Information:\n"
    if (!basicVariables.isEmpty)
      finalString += basicVariables.map(x => x.toString).mkString("", "\n", "\n")
    if (!allCollections.isEmpty)
      finalString += allCollections.map(x => x.toString).mkString("", "\n", "\n")
    if (!allBasicHeaps.filter(y => !y._2.basicHeapEntries.isEmpty).isEmpty)
      finalString += allBasicHeaps.reverse.filter(y => !y._2.basicHeapEntries.isEmpty).map(x => "   " + x._1 + " Heap: \n" + x._2.toString).mkString("", "\n", "\n")
    if (!DomainEntries.isEmpty || !nonDomainFunctions.isEmpty)
      finalString ++= "   Domains:\n"
    if (!DomainEntries.isEmpty)
      finalString += DomainEntries.map(x => x.toString).mkString("", "\n", "\n")
    if (!nonDomainFunctions.isEmpty)
      finalString += nonDomainFunctions.map(x => x.toString).mkString("", "\n", "\n")
    finalString
  }
}

object IntermediateCounterexampleModel {
  /**
    * Determines the local variables and their value.
    */
  def detCEvariables(originalEntries: Map[String, ModelEntry], namesInMember: Map[String, String], variables: Seq[Declaration]): (Seq[CEVariable], Seq[Declaration]) = {
    var res = Seq[CEVariable]()
    var otherDeclarations = Seq[Declaration]()
    val modelVariables = transformModelEntries(originalEntries, namesInMember)
    for ((name, entry) <- modelVariables) {
      for (temp <- variables) {
        if (temp.isInstanceOf[ast.LocalVarDecl]) {
          val v = temp.asInstanceOf[ast.LocalVarDecl]
          if (v.name == name) {
            var ent = entry
            if (entry.isInstanceOf[MapEntry]) {
              ent = entry.asInstanceOf[MapEntry].options.head._1(0)
            }
            res +:= CEVariable(v.name, ent, Some(v.typ))
          }
        } else {
          otherDeclarations +:= temp
        }
      }
    }
    if (originalEntries.contains("null")) {
      val nullRef = originalEntries.get("null").get
      if (nullRef.isInstanceOf[ConstantEntry]) {
        res +:= CEVariable("null", nullRef, Some(ast.Ref))
      }
    }
    (res, otherDeclarations)
  }

  /**
    * Chooses the latest instance of a variable in the counterexample model received from the SMT solver.
    */
  def transformModelEntries(originalEntries: Map[String, ModelEntry], namesInMember: Map[String, String]): mutable.Map[String, ModelEntry] = {
    val newEntries = mutable.HashMap[String, ModelEntry]()
    val currentEntryForName = mutable.HashMap[String, String]()
    for ((vname, e) <- originalEntries) {
      var originalName = vname
      if (originalName.startsWith("q@")) {
        originalName = originalName.substring(2)
      } else if (originalName.indexOf("@@") != -1) {
        originalName = originalName.substring(0, originalName.indexOf("@@"))
      } else if (originalName.indexOf("@") != -1) {
        originalName = originalName.substring(0, originalName.indexOf("@"))
      }
      if (PrettyPrinter.backMap.contains(originalName)) {
        val originalViperName = PrettyPrinter.backMap.get(originalName).get
        if (namesInMember.contains(originalViperName)) {
          val viperName = namesInMember.get(originalViperName).get
          if (!currentEntryForName.contains(viperName) ||
            isLaterVersion(vname, originalName, currentEntryForName.get(viperName).get)) {
            newEntries.update(viperName, e)
            currentEntryForName.update(viperName, vname)
          }
        }
      }
    }
    newEntries
  }

  def isLaterVersion(firstName: String, originalName: String, secondName: String): Boolean = {
    if ((secondName == originalName || secondName == "q@" + originalName || secondName.indexOf("@@") != -1) && !"@@.*!".r.findFirstIn(firstName).isDefined) {
      true
    } else if (secondName.indexOf("@") != -1 && firstName.indexOf("@@") == -1 && firstName.indexOf("@") != -1) {
      val firstIndex = Integer.parseInt(firstName.substring(firstName.indexOf("@") + 1))
      val secondIndex = Integer.parseInt(secondName.substring(secondName.indexOf("@") + 1))
      firstIndex > secondIndex
    } else {
      false
    }
  }

  /**
    * Generates the sequences of the CE.
    */
  def detSequences(model: Model): Set[CEValue] = {
    var res = Map[String, Seq[String]]()
    var tempMap = Map[(String, Seq[String]), String]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Seq#Length") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (k(0).toString -> Seq.fill(v.toString.toInt)("#undefined"))
          }
        }
      } else if (opName == "Seq#Empty") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Seq())
          }
        }
      } else if (opName == "Seq#Append" || opName == "Seq#Take" || opName == "Seq#Drop" || opName == "Seq#Index") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    for ((opName, opValues) <- model.entries) {
      if (opName == "Seq#Singleton") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Seq(k(0).toString))
          }
        }
      }
      if (opName == "Seq#Range") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Seq.range(k(0).toString.toInt, k(1).toString.toInt).map(x => x.toString))
          }
        }
      }
    }
    var found = true
    while (found) {
      found = false
      for (((opName, k), v) <- tempMap) {
        if (opName == "Seq#Append") {
          (res.get(k(0)), res.get(k(1))) match {
            case (Some(x), Some(y)) =>
              if (!res.contains(v)) {
                res += (v -> (x ++ y))
                tempMap -= ((opName, k))
                found = true
              }
            case (_, _) => //
          }
        } else if (opName == "Seq#Take") {
          res.get(k(0)) match {
            case Some(x) =>
              res += (v -> x.take(k(1).toInt))
              tempMap -= ((opName, k))
              found = true
            case None => //
          }
        } else if (opName == "Seq#Drop") {
          res.get(k(0)) match {
            case Some(x) =>
              res += (v -> x.drop(k(1).toInt))
              tempMap -= ((opName, k))
              found = true
            case None => //
          }
        } else if (opName == "Seq#Index") {
          res.get(k(0)) match {
            case Some(x) =>
              if (!k(1).startsWith("(")) {
                res += (k(0) -> x.updated(k(1).toInt, v))
                found = true
              }
              tempMap -= ((opName, k))
            case None => //
          }
        }
      }
    }
    var ans = Set[CEValue]()
    res.foreach {
      case (n, s) =>
        val typ: Option[Type] = detASTTypeFromString(n.replaceAll(".*?<(.*)>.*", "$1")) match {
          case Some(x) => Some(ast.SeqType(x))
          case None => None
        }
        var entries = Map[BigInt, String]()
        var counter = 0
        for (e <- s) {
          if (e != "#undefined") {
            entries += (BigInt(counter) -> e)
          }
          counter += 1
        }
        ans += CESequence(n, BigInt(s.length), entries, s, typ)
    }
    ans
  }

  /**
    * Generates the sets of the CE.
    */
  def detSets(model: Model): Set[CEValue] = {
    var res = Map[String, Set[String]]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Set#Empty") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Set())
          }
        } else if (opValues.isInstanceOf[ConstantEntry] && opValues.asInstanceOf[ConstantEntry].value != "false" && opValues.asInstanceOf[ConstantEntry].value != "true") {
          res += (opValues.asInstanceOf[ConstantEntry].value -> Set())
        }
      }
      if (opName == "Set#Singleton") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Set(k(0).toString))
          }
        }
      }
      if (opName == "Set#Card") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            if (v.toString.startsWith("0")) {
              res += (k(0).toString -> Set())
            }
          }
        }
      }
      if (opName == "MapType2Select") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            if (v.toString.toBoolean) {
              if (k(1).toString.startsWith("T@U!val!")) {
                res += (k(0).toString -> Set())
              } else {
                res += (k(0).toString -> Set())
              }
            }
          }
        }
      }
    }
    var tempMap = Map[(String, Seq[String]), String]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Set#UnionOne" || opName == "MapType2Select") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        if (opName == "Set#UnionOne") {
          res.get(k(0)) match {
            case Some(x) =>
              res += (v -> x.union(Set(k(1))))
              tempMap -= ((opName, k))
            case None => //
          }
        } else if (opName == "MapType2Select") {
          res.get(k(0)) match {
            case Some(x) =>
              if (v.toBoolean && !k(1).startsWith("T@U!val!")) {
                res += (k(0) -> x.union(Set(k(1))))
              }
            case None =>
              if (v.toBoolean && !k(1).startsWith("T@U!val!")) {
                res += (k(0) -> Set(k(1)))
              } else {
                res += (k(0) -> Set())
              }
          }
          tempMap -= ((opName, k))
        }
      }
    }
    for ((opName, opValues) <- model.entries) {
      if (opName == "Set#Union" || opName== "Set#Difference" || opName == "Set#Intersection") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    var found = true
    while (!tempMap.isEmpty && found) {
      found = false
      for (((opName, k), v) <- tempMap) {
        val firstSet = res.get(k(0))
        val secondSet = res.get(k(1))
        if ((firstSet != None) && (secondSet != None)) {
          if (opName == "Set#Union") {
            res += (v -> firstSet.get.union(secondSet.get))
            tempMap -= ((opName, k))
            found = true
          } else if (opName == "Set#Intersection") {
            res += (v -> firstSet.get.intersect(secondSet.get))
            tempMap -= ((opName, k))
            found = true
          } else if (opName == "Set#Difference") {
            res += (v -> firstSet.get.diff(secondSet.get))
            tempMap -= ((opName, k))
            found = true
          }
        }
      }
    }
    var ans = Set[CEValue]()
    res.foreach {
      case (n, s) =>
        val typ: Option[Type] = detASTTypeFromString(n.replaceAll(".*?<(.*)>.*", "$1")) match {
          case Some(x) => Some(ast.SetType(x))
          case None => None
        }
        var containment = Map[String, Boolean]()
        for (e <- s) {
          if (e != "#undefined") {
            containment += (e -> true)
          }
        }
        ans += CESet(n, BigInt(s.size), containment, s, typ)
    }
    ans
  }

  /**
    * Generates the multisets of the CE.
    */
  def detMultisets(model: Model): Set[CEValue] = {
    var res = Map[String, Map[String, Int]]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "MultiSet#Empty") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Map[String, Int]())
          }
        } else if (opValues.isInstanceOf[ConstantEntry] && opValues.asInstanceOf[ConstantEntry].value != "false" && opValues.asInstanceOf[ConstantEntry].value != "true") {
          res += (opValues.asInstanceOf[ConstantEntry].value -> Map[String, Int]())
        }
      }
      if (opName == "MultiSet#Singleton") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Map(k(0).toString -> 1))
          }
        }
      }
      if (opName == "MultiSet#Select") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            if (!k(1).toString.startsWith("T@U!val!") && !v.toString.startsWith("0")) {
              res += (k(0).toString -> res.getOrElse(k(0).toString, Map.empty).updated(k(1).toString, v.toString.toInt))
            }
          }
        }
      }
      if (opName == "MultiSet#Card") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            if (v.toString.startsWith("0")) {
              res += (k(0).toString -> Map[String, Int]())
            }
          }
        }
      }
    }
    var tempMap = Map[(String, Seq[String]), String]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "MultiSet#UnionOne") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        res.get(k(0)) match {
          case Some(x) =>
            res += (v -> x.updated(k(1), x.getOrElse(k(1), 0)+1))
            tempMap -= ((opName, k))
          case None => //
        }
      }
    }
    for ((opName, opValues) <- model.entries) {
      if (opName == "MultiSet#Union" || opName == "MultiSet#Difference" || opName == "MultiSet#Intersection") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        val firstMultiset = res.get(k(0))
        val secondMultiset = res.get(k(1))
        if ((firstMultiset != None) && (secondMultiset != None)) {
          if (opName == "MultiSet#Union") {
            res += (v -> (firstMultiset.get.keySet ++ secondMultiset.get.keySet).map { key =>
              (key -> (firstMultiset.get.getOrElse(key, 0) + secondMultiset.get.getOrElse(key, 0)))
            }.toMap)
            tempMap -= ((opName, k))
          } else if (opName == "MultiSet#Intersection") {
            res += (v -> (firstMultiset.get.keySet & secondMultiset.get.keySet).map { key =>
              key -> Math.min(firstMultiset.get.get(key).get, secondMultiset.get.get(key).get)
            }.toMap)
            tempMap -= ((opName, k))
          } else if (opName == "MultiSet#Difference") {
            res += (v -> (firstMultiset.get.map { case (key, count) =>
              key -> (count - secondMultiset.get.getOrElse(key, 0))
            }.filter(_._2 > 0) ++ secondMultiset.get.filter { case (key, _) =>
              !firstMultiset.get.contains(key)
            }))
            tempMap -= ((opName, k))
          }
        }
      }
    }
    var ans = Set[CEValue]()
    res.foreach {
      case (n, s) =>
        val typ: Option[Type] = detASTTypeFromString(n.replaceAll(".*?<(.*)>.*", "$1")) match {
          case Some(x) => Some(ast.SetType(x))
          case None => None
        }
        val size = s.values.sum
        ans += CEMultiset(n, BigInt(size), s, typ)
    }
    ans
  }

  def detASTTypeFromString(typ: String): Option[Type] = {
    typ match {
      case "Int" => Some(ast.Int)
      case "Bool" => Some(ast.Bool)
      case "Perm" => Some(ast.Perm)
      case "Ref" => Some(ast.Ref)
      case _ => None
    }
  }

  /**
    * Takes the counterexample model received from the SMT solver and restructures it.
    */
  def buildNewModel(originalEntries: Map[String, ModelEntry]): Map[Seq[String], String] = {
    var newEntriesMapping = Map[Seq[String], String]()
    for ((key, value) <- originalEntries) {
      if (value.isInstanceOf[ConstantEntry]) {
        val valConstEntry = value.asInstanceOf[ConstantEntry]
        newEntriesMapping += (Seq(key) -> valConstEntry.toString)
      } else if (value.isInstanceOf[MapEntry]) {
        val tempMapping = value.asInstanceOf[MapEntry].options
        for ((keyTM, valueTM) <- tempMapping) {
          val tempSeq = (keyTM.map(x => x.toString))
          if (tempSeq.contains("else")) {
            //
          } else {
            newEntriesMapping += (Seq(key) ++ tempSeq -> valueTM.toString)
          }
        }
      } else if (value.isInstanceOf[ApplicationEntry]) {
        val applEntry = value.asInstanceOf[ApplicationEntry]
        newEntriesMapping += (Seq(key) -> applEntry.toString)
      } else if (value.toString != UnspecifiedEntry.toString) {
        println("error in buildNewModel")
      }
    }
    newEntriesMapping
  }

  /**
    * Gather all the heap and mask states from the model. Then, combine them into heap instances (=> mask state + heap state)
    * and order them.
    */
  def oldAndReturnHeapMask(workingModel: Map[Seq[String], String], labels: Seq[Declaration]): (Map[String, (String, String)], List[(String, String, String, String)]) = {
    var heapInstances = Set[(String, String)]()
    var maskInstances = Set[(String, String)]()
    var states = Set[(String, String)]()
    for ((k, v) <- workingModel) {
      if (k(0).startsWith("Heap@@")) {
        heapInstances += ((k(0), v))
      } else if (k(0).startsWith("Mask@@")) {
        maskInstances += ((k(0), v))
      } else if (k(0).startsWith("Heap@")) {
        heapInstances += ((k(0), v))
      } else if (k(0).startsWith("Mask@")) {
        maskInstances += ((k(0), v))
      } else if (k(0).startsWith("QPMask@")) {
        maskInstances += ((k(0).stripPrefix("QP").trim, v))
      } else if ((k(0) == "state") && (v == "true")) {
        states += ((k(1), k(2)))
      }
    }

    // determine all the heap and mask states (first all, then sorted and then filtered)
    val hmStates = for {
      (heapId, maskId) <- states
      hName <- heapInstances.collect { case (name, id) if id == heapId => name }
      mName <- maskInstances.collect { case (name, id) if id == maskId => name }
    } yield (hName, mName, heapId, maskId)

    val sortedHMStates = hmStates.toList.sortBy {
      case (heapName, maskName, _, _) =>
        if (heapName.startsWith("Heap@@") && maskName.startsWith("Mask@@")) {
          0
        } else if (heapName.startsWith("Heap@@")) {
          val maskValue = maskName.stripPrefix("Mask@").trim.toInt
          maskValue + 1
        } else if (maskName.startsWith("Mask@@")) {
          val heapValue = heapName.stripPrefix("Heap@").trim.toInt
          heapValue + 1
        } else {
          val heapValue = heapName.stripPrefix("Heap@").trim.toInt
          val maskValue = maskName.stripPrefix("Mask@").trim.toInt
          heapValue + maskValue + 2
        }
    }

    val filteredList = sortedHMStates.foldLeft(List.empty[(String, String, String, String)]) {
      case (acc, curr@(h, m, _, _))
        if h.contains("@@") || m.contains("@@") || acc.isEmpty || acc.last._1.contains("@@") || acc.last._2.contains("@@") || (h.stripPrefix("Heap@").trim.toInt >= acc.last._1.stripPrefix("Heap@").trim.toInt && m.stripPrefix("Mask@").trim.toInt >= acc.last._2.stripPrefix("Mask@").trim.toInt) =>
        acc :+ curr
      case (acc, _) =>
        acc
    }

    var labelsHeapMask = Map[String, (String, String)]()
    labelsHeapMask += ("old" -> (filteredList(0)._3, filteredList(0)._4))
    for (l <- labels) {
      l match {
        case ast.Label(n, _) =>
          val lhi = "Label" + n + "Heap"
          val lmi = "Label" + n + "Mask"
          if (workingModel.contains(Seq(lhi)) && workingModel.contains(Seq(lmi))) {
            labelsHeapMask += (n -> (workingModel.get(Seq(lhi)).get, workingModel.get(Seq(lmi)).get))
          }
        case _ => //
      }
    }
    labelsHeapMask += ("return" -> (filteredList(filteredList.length-1)._3, filteredList(filteredList.length-1)._4))

    (labelsHeapMask, filteredList)
  }

  /**
    * Determines all the heap resources by iterating through the heap instances: Check all the "MapType0Select" function
    * for the heap state of the heap instance and check the "MapType0Select" function for the mask state of the heap
    * instance. Then gather all the heap resources that occur in both functions for a specific heap instance.
    * @param MapType0Select Mappings from a heap state, a reference and a field to a value.
    * @param MapType0Select Mappings from a mask state, a reference and a field to a permission.
    * The fields in these mappings can also be identifiers for a predicate or a magic wand.
    */
  def detHeaps(opMapping: Map[Seq[String], String], hmStates: List[(String, String, String, String)], model: Model, hmLabels: Map[String, (String, String)], program: Program): Seq[(String, BasicHeap)] = {
    val predByName = program.predicatesByName
    var heapOp = Map[Seq[String], String]()
    var maskOp = Map[Seq[String], String]()
    var qpMaskSet = Set[String]()
    for ((key, value) <- opMapping) {
      if (key(0).startsWith("MapType0Select")) {
        heapOp += (key -> value)
      } else if (key(0).startsWith("MapType1Select")) {
        maskOp += (key -> value)
      } else if (key(0).startsWith("QPMask@")) {
        qpMaskSet += value
      }
    }
    var predContentMap = Map[String, Seq[String]]()
    var predicateFinder = Map[String, String]()
    for (predName <- program.predicates.map(x => x.name)) {
      val predEntry = model.entries.get(predName).getOrElse(model.entries.find{ case (x, _) => (x.startsWith(predName ++ "_") && !x.contains("@"))}.getOrElse(ConstantEntry("")))
      if (predEntry.isInstanceOf[MapEntry] && !predEntry.asInstanceOf[MapEntry].options.isEmpty) {
        for ((predContent, predId) <- predEntry.asInstanceOf[MapEntry].options) {
          predContentMap += (predId.toString -> predContent.map(x => x.toString))
          predicateFinder += (predId.toString -> predName)
        }
      }
    }
    var mwContentMap = Map[String, Seq[String]]()
    for ((k,v) <- model.entries) {
      if (k == "wand" || (k.startsWith("wand" ++ "_") && !k.contains("@"))) {
        if (v.isInstanceOf[MapEntry] && !v.asInstanceOf[MapEntry].options.isEmpty) {
          for ((mwContent, mwId) <- v.asInstanceOf[MapEntry].options) {
            mwContentMap += (mwId.toString -> mwContent.map(x => x.toString))
          }
        }
      }
    }
    val permMap = model.entries.get("U_2_real").get.asInstanceOf[MapEntry].options
    var res = Seq[(String, BasicHeap)]()
    for ((labelName, (labelHeap, labelMask)) <- hmLabels) {
      var heapEntrySet = Set[BasicHeapEntry]()
      val heapStore = model.entries.get("MapType0Store").get.asInstanceOf[MapEntry].options
      val maskStore = model.entries.get("MapType1Store").get.asInstanceOf[MapEntry].options
      val heapMap = recursiveBuildHeapMask(heapStore, labelHeap, Map.empty)
      val maskMap = recursiveBuildHeapMask(maskStore, labelMask, Map.empty)
      val commonKeys = heapMap.keys.toSet.intersect(maskMap.keys.toSet)
      for (ck <- commonKeys) {
        val value = heapMap.get(ck).get
        val perm = maskMap.get(ck).get
        val tempPerm: Option[Rational] = detHeapEntryPermission(permMap, perm._1)
        val typ: HeapEntryType = detHeapType(model, qpMaskSet, ck(1), perm._2)
        if (typ == FieldType || typ == QPFieldType) {
          heapEntrySet += BasicHeapEntry(Seq(ck(0)), Seq(ck(1)), value._1, tempPerm, typ, None)
        } else if (typ == PredicateType || typ == QPPredicateType) {
          heapEntrySet += BasicHeapEntry(Seq(ck(0), ck(1)), predContentMap.get(ck(1)).getOrElse(Seq()), value._1, tempPerm, typ, Some(evalInsidePredicate(value._1, ck(1), predicateFinder, predByName, model)))
        } else if (typ == MagicWandType || typ == QPMagicWandType) {
          heapEntrySet += BasicHeapEntry(Seq(ck(0), ck(1)), predContentMap.get(ck(1)).getOrElse(Seq()), value._1, tempPerm, typ, None)
        }
      }
      var startNow = false
      for ((_, _, heapIdentifier, maskIdentifier) <- hmStates.reverse) {
        if (heapIdentifier == labelHeap && maskIdentifier == labelMask) {
          startNow = true
        }
        if (startNow) {
          for ((maskKey, perm) <- maskOp) {
            val maskId = maskKey(1)
            val reference = maskKey(2)
            val field = maskKey(3)
            if (maskId == maskIdentifier) {
              if (!heapEntrySet.exists({
                case bhe =>
                  ((bhe.reference.length > 0) && (bhe.field.length > 0) && (bhe.reference(0) == reference) && (bhe.field(0) == field)) ||
                    ((bhe.reference.length > 1) && (bhe.reference(0) == reference) && (bhe.reference(1) == field))
              })) {
                val tempPerm: Option[Rational] = detHeapEntryPermission(permMap, perm)
                val typ: HeapEntryType = detHeapType(model, qpMaskSet, field, maskId)
                if (typ == FieldType || typ == QPFieldType) {
                  heapOp.get(Seq("MapType0Select", heapIdentifier, reference, field)) match {
                    case Some(v) => heapEntrySet += BasicHeapEntry(Seq(reference), Seq(field), v, tempPerm, typ, None)
                    case None => heapEntrySet += BasicHeapEntry(Seq(reference), Seq(field), "#undefined", tempPerm, typ, None)
                  }
                } else if (typ == PredicateType || typ == QPPredicateType) {
                  heapOp.get(Seq("MapType0Select", heapIdentifier, reference, field)) match {
                    case Some(v) => heapEntrySet += BasicHeapEntry(Seq(reference, field), predContentMap.get(field).getOrElse(Seq()), v, tempPerm, typ, Some(evalInsidePredicate(v, field, predicateFinder, predByName, model)))
                    case None => heapEntrySet += BasicHeapEntry(Seq(reference, field), predContentMap.get(field).getOrElse(Seq()), "#undefined", tempPerm, typ, Some(Map[ast.Exp, ModelEntry]()))
                  }
                } else if (typ == MagicWandType || typ == QPMagicWandType) {
                  heapOp.get(Seq("MapType0Select", heapIdentifier, reference, field)) match {
                    case Some(v) => heapEntrySet += BasicHeapEntry(Seq(reference, field), mwContentMap.get(field).getOrElse(Seq()), v, tempPerm, typ, None)
                    case None => heapEntrySet += BasicHeapEntry(Seq(reference, field), mwContentMap.get(field).getOrElse(Seq()), "#undefined", tempPerm, typ, None)
                  }
                }
              } else {
                heapEntrySet.find(
                  { case bhe => (bhe.het == FieldType || bhe.het == QPFieldType) && (bhe.reference(0) == reference) && (bhe.field(0) == field) && (bhe.valueID == "#undefined") }
                ) match {
                  case Some(v) =>
                    heapOp.get(Seq("MapType0Select", heapIdentifier, reference, field)) match {
                      case Some(x) =>
                        heapEntrySet += BasicHeapEntry(Seq(reference), Seq(field), x, v.perm, v.het, None)
                        heapEntrySet -= BasicHeapEntry(Seq(reference), Seq(field), "#undefined", v.perm, v.het, None)
                      case None => //
                    }
                  case None => //
                }
                heapEntrySet.find(
                  { case bhe => (bhe.het == PredicateType || bhe.het == QPPredicateType) && (bhe.reference(0) == reference) && (bhe.reference(1) == field) && (bhe.valueID == "#undefined") }
                ) match {
                  case Some(v) =>
                    heapOp.get(Seq("MapType0Select", heapIdentifier, reference, field)) match {
                      case Some(x) =>
                        heapEntrySet += BasicHeapEntry(Seq(reference, field), predContentMap.get(field).getOrElse(Seq()), x, v.perm, v.het, v.insidePredicate)
                        heapEntrySet -= BasicHeapEntry(Seq(reference, field), predContentMap.get(field).getOrElse(Seq()), "#undefined", v.perm, v.het, v.insidePredicate)
                      case None => //
                    }
                  case None => //
                }
                heapEntrySet.find(
                  { case bhe => (bhe.het == MagicWandType || bhe.het == QPMagicWandType) && (bhe.reference(0) == reference) && (bhe.reference(1) == field) && (bhe.valueID == "#undefined") }
                ) match {
                  case Some(v) =>
                    heapOp.get(Seq("MapType0Select", heapIdentifier, reference, field)) match {
                      case Some(x) =>
                        heapEntrySet += BasicHeapEntry(Seq(reference, field), mwContentMap.get(field).getOrElse(Seq()), x, v.perm, v.het, None)
                        heapEntrySet -= BasicHeapEntry(Seq(reference, field), mwContentMap.get(field).getOrElse(Seq()), "#undefined", v.perm, v.het, None)
                      case None => //
                    }
                  case None => //
                }
              }
            }
          }
        }
      }
      res +:= (labelName, BasicHeap(heapEntrySet))
    }
    res
  }

  /**
    * Evaluate the snapshot of a predicate.
    */
  def evalInsidePredicate(insId: String, predId: String, predicateFinder: Map[String, String], predByName: scala.collection.immutable.Map[String, Predicate], model: Model): Map[ast.Exp, ModelEntry] = {
    val frameAssign = model.entries.get("FrameFragment")
    val frameCombine = model.entries.get("CombineFrames")
    var ans = scala.collection.immutable.Map[ast.Exp, ModelEntry]()
    if (frameAssign.isDefined && frameAssign.get.isInstanceOf[MapEntry] && frameCombine.isDefined && frameCombine.get.isInstanceOf[MapEntry]) {
      val insTerm: Seq[String] = detInsideTerm(frameCombine.get.asInstanceOf[MapEntry].options.map(_.swap), insId, Seq())
      val evaluatedPredTerm = insTerm.map(ent => detInsideValue(frameAssign.get.asInstanceOf[MapEntry].options.map(_.swap), ent))
      val predName = predicateFinder.get(predId)
      if (predName.isDefined && predByName.get(predName.get).isDefined) {
        val astPred = predByName.get(predName.get)
        if (astPred.isDefined && !astPred.get.isAbstract) {
          val predBody = astPred.get.body.get
          val insPred = insPredToBody(predBody, evaluatedPredTerm)
          if (insPred.length > 0 && !(insPred.length == 1 && insPred(0)._2.startsWith("T@U!val!"))) {
            var assignedPredBody = scala.collection.immutable.Map[ast.Exp, ModelEntry]()
            for ((exp, value) <- insPred) {
              if (value.startsWith("T@U!val!") || value.startsWith("(T@U!val!")) {
                assignedPredBody += evalBody(exp, UnspecifiedEntry, assignedPredBody)
              } else {
                assignedPredBody += evalBody(exp, ConstantEntry(value), assignedPredBody)
              }
            }
            ans = assignedPredBody
          }
        }
      }
    }
    ans
  }

  /**
    * Compare the snapshot of a predicate to its actual body (accessed through its ast node).
    */
  def evalBody(exp: ast.Exp, value: ModelEntry, lookup: Map[ast.Exp, ModelEntry]): (ast.Exp, ModelEntry) = {
    exp match {
      case ast.FieldAccessPredicate(predAcc, _) => (predAcc, value)
      case ast.CondExp(cond, thn, els) =>
        if (evalExp(cond, lookup)) {
          evalBody(thn, value, lookup)
        } else {
          evalBody(els, value, lookup)
        }
      case ast.Implies(left, right) =>
        if (evalExp(left, lookup)) {
          evalBody(right, value, lookup)
        } else {
          (left, ConstantEntry("False"))
        }
      case _ => (exp, value)
    }
  }

  def evalExp(exp: ast.Exp, lookup: scala.collection.immutable.Map[ast.Exp, ModelEntry]): Boolean = exp match {
    case ast.NeCmp(left, right) => !lookup.getOrElse(left, left.toString()).toString.equalsIgnoreCase(lookup.getOrElse(right, right.toString()).toString)
    case ast.EqCmp(left, right) => (lookup.getOrElse(left, ConstantEntry(left.toString())).toString.equalsIgnoreCase(lookup.getOrElse(right, ConstantEntry(right.toString())).toString))
    case _ => false
  }

  def insPredToBody(body: ast.Exp, insPred: Seq[String]): Seq[(ast.Exp, String)] = {
    if (insPred.length == 0) {
      Seq()
    } else if (insPred.length == 1) {
      Seq((body, insPred(0)))
    } else {
      if (body.subExps.length == 2) {
        Seq((body.subExps(0), insPred(0))) ++ insPredToBody(body.subExps(1), insPred.tail)
      } else {
        Seq()
      }
    }
  }

  def detInsideValue(framesAssign: Map[ValueEntry, Seq[ValueEntry]], entry: String): String = {
    if (framesAssign.contains(ConstantEntry(entry))) {
      detInsideValue(framesAssign, framesAssign.get(ConstantEntry(entry)).get(0).toString)
    } else {
      entry
    }
  }

  def detInsideTerm(framesCombine: Map[ValueEntry, Seq[ValueEntry]], insId: String, term: Seq[String]): Seq[String] = {
    if (framesCombine.contains(ConstantEntry(insId))) {
      val newterm = term ++ framesCombine.get(ConstantEntry(insId)).get.map(x => x.toString)
      detInsideTerm(framesCombine, newterm(newterm.length-1), newterm)
    } else {
      term
    }
  }

  /**
    * Determine the type of a heap resource.
    */
  def detHeapType(model: Model, qpMaskSet: Set[String], id: String, maskId: String): HeapEntryType = {
    var predIdSet = Set[String]()
    if (model.entries.get("IsPredicateField").get.isInstanceOf[MapEntry]) {
      for ((k, v) <- model.entries.get("IsPredicateField").get.asInstanceOf[MapEntry].options) {
        if (v.toString == "true") {
          predIdSet += k(0).toString
        }
      }
    }
    var mwIdSet = Set[String]()
    if (model.entries.get("IsWandField").get.isInstanceOf[MapEntry]) {
      for ((k, v) <- model.entries.get("IsWandField").get.asInstanceOf[MapEntry].options) {
        if (v.toString == "true") {
          mwIdSet += k(0).toString
        }
      }
    }
    var typ: HeapEntryType = FieldType
    if (predIdSet.contains(id)) {
      if (qpMaskSet.contains(maskId)) {
        typ = QPPredicateType
      } else {
        typ = PredicateType
      }
    } else if (mwIdSet.contains(id)) {
      if (qpMaskSet.contains(maskId)) {
        typ = QPMagicWandType
      } else {
        typ = MagicWandType
      }
    } else {
      if (qpMaskSet.contains(maskId)) {
        typ = QPFieldType
      }
    }
    typ
  }

  def detHeapEntryPermission(permMap: Map[scala.collection.immutable.Seq[ValueEntry], ValueEntry], perm: String): Option[Rational] = {
    for ((s, ve) <- permMap) {
      if (s(0).toString == perm) {
        if (ve.isInstanceOf[ConstantEntry]) {
          return Some(Rational.apply(BigInt(ve.asInstanceOf[ConstantEntry].value.toFloat.toInt), BigInt(1)))
        } else if (ve.isInstanceOf[ApplicationEntry]) {
          val ae = ve.asInstanceOf[ApplicationEntry]
          return Some(Rational.apply(BigInt(ae.arguments(0).asInstanceOf[ConstantEntry].value.toFloat.toInt), BigInt(ae.arguments(1).asInstanceOf[ConstantEntry].value.toFloat.toInt)))
        }
      }
    }
    None
  }

  def recursiveBuildHeapMask(inputMap: Map[scala.collection.immutable.Seq[ValueEntry], ValueEntry], s: String, resultMap: Map[Seq[String], (String, String)]): Map[Seq[String], (String, String)] = {
    val entries: Iterable[(Seq[ValueEntry], ValueEntry)] = inputMap.collect {
      case (key, value) if value.toString == s && key.length >= 3 => (key, value)
    }
    if (entries.isEmpty) {
      return resultMap
    }
    entries.foldLeft (resultMap) {
      case (accMap, (entry, value)) =>
        val newStartString = entry(0)
        val newKey = entry.tail.init.map(x => x.toString)
        var newResultMap = accMap
        if (!accMap.contains(newKey)) {
          newResultMap += (newKey -> (entry.last.toString, value.toString))
        }
        recursiveBuildHeapMask(inputMap, newStartString.toString, newResultMap)
    }
  }

  /**
    * Extracts domains from a program. Only the ones that are used in the program... no generics.
    * It also extracts all instances (translates the generics to concrete values).
    */
  def getAllDomains(model: Model, program: ast.Program): Seq[BasicDomainEntry] = {
    val domains = program.collect {
      case a: ast.Domain => a
    }
    val concreteDoms = program.collect {
      case ast.DomainType(n, map) => (n, map)
      case d: ast.DomainFuncApp => (d.domainName, d.typVarMap)
    }.filterNot(x => containsTypeVar(x._2.values.toSeq)).toSet
    val doms = domains.flatMap(x => if (x.typVars == Nil) Seq((x, Map.empty[ast.TypeVar, ast.Type])) else concreteDoms.filter(_._1 == x.name).map(y => (x, y._2))) // changing the typevars to the actual ones
    doms.map(x => {
      val types = try {
        x._1.typVars.map(x._2)
      } catch {
        case _: Throwable => Seq()
      }
      val translatedFunctions = x._1.functions.map(y => detFunction(model, y, x._2, Seq(), program, false))
      BasicDomainEntry(x._1.name, types, translatedFunctions)
    }).toSeq
  }

  def containsTypeVar(s: Seq[ast.Type]): Boolean = s.exists(x => x.isInstanceOf[ast.TypeVar])

  /**
    * Extract all the functions occuring inside of a domain.
    */
  def getAllFunctions(model: Model, program: ast.Program, heapInstances: Seq[(String, String, String, String)]): Seq[BasicFunction] = {
    val funcs = program.collect {
      case f: ast.Function => f
    }
    funcs.map(x => detFunction(model, x, Map.empty, heapInstances, program, true)).toSeq
  }

  /**
    * Determine all the inputs and outputs combinations of a function occruing the counterexample model.
    */
  def detFunction(model: Model, func: ast.FuncLike, genmap: scala.collection.immutable.Map[ast.TypeVar, ast.Type], heapInst: Seq[(String, String, String, String)], program: ast.Program, hd: Boolean): BasicFunction = {
    val fname = func.name
    val resTyp: ast.Type = func.typ
    val argTyp: Seq[ast.Type] = func.formalArgs.map(x => x.typ)
    model.entries.get(fname) match {
      case Some(MapEntry(m, els)) =>
        var options = Map[Seq[String], String]()
        if (hd) {
          for ((k, v) <- m) {
            var hName = k.head.toString
            for ((h, _, i, _) <- heapInst) {
              if (i == hName) {
                hName = h
              }
            }
            options += (Seq(hName) ++ k.tail.map(x => x.toString) -> v.toString)
          }
        } else {
          for ((k, v) <- m) {
            options += (k.map(x => x.toString) -> v.toString)
          }
        }
        BasicFunction(fname, argTyp, resTyp, options, els.toString)
      case Some(ConstantEntry(t)) => BasicFunction(fname, argTyp, resTyp, Map.empty, t)
      case Some(ApplicationEntry(n, args)) => BasicFunction(fname, argTyp, resTyp, Map.empty, ApplicationEntry(n, args).toString)
      case Some(x) => BasicFunction(fname, argTyp, resTyp, Map.empty, x.toString)
      case None => BasicFunction(fname, argTyp, resTyp, Map.empty, "#undefined")
    }
  }

}

object CounterexampleGenerator {
  /**
    * Combine a local variable with its ast node.
    */
  def detStore(store: Seq[Declaration], variables: Seq[CEVariable], collections: Set[CEValue]): (StoreCounterexample, Map[String, (String, Int)]) = {
    var refOccurences = Map[String, (String, Int)]()
    var ans = Seq[StoreEntry]()
    for (k <- store) {
      if (k.isInstanceOf[ast.LocalVarDecl]) {
        val v = k.asInstanceOf[ast.LocalVarDecl]
        for (vari <- variables) {
          if (v.name == vari.name) {
            if (v.typ == ast.Ref) {
              if (refOccurences.get(vari.entryValue.toString).isDefined) {
                val (n, i) = refOccurences.get(vari.entryValue.toString).get
                if (n != v.name) {
                  refOccurences += (vari.entryValue.toString -> (v.name, i + 1))
                }
              } else {
                refOccurences += (vari.entryValue.toString -> (v.name, 1))
              }
            }
            var found = false
            for (coll <- collections) {
              if (vari.entryValue.toString == coll.id) {
                ans +:= StoreEntry(ast.LocalVar(v.name, v.typ)(), coll)
                found = true
              }
            }
            if (!found) {
              ans +:= StoreEntry(ast.LocalVar(v.name, v.typ)(), vari)
            }
          }
        }
      }
    }
    (StoreCounterexample(ans), refOccurences)
  }

  /**
    * Match the collection type for the "extended" CE.
    */
  def detTranslationMap(store: StoreCounterexample, fields: Map[String, (String, Int)]): Map[String, String] = {
    var namesTranslation = Map[String, String]()
    for (ent <- store.storeEntries) {
      ent.entry match {
        case CEVariable(internalName, entryValue, _) => namesTranslation += (entryValue.toString -> ent.id.name)
        case CESequence(internalName, _, _, _, _) => namesTranslation += (internalName -> (ent.id.name + " (Seq)"))
        case CESet(internalName, _, _, _, _) => namesTranslation += (internalName -> (ent.id.name + " (Set)"))
        case CEMultiset(internalName, _, _, _) => namesTranslation += (internalName -> (ent.id.name + " (MultiSet)"))
      }
    }
    for ((k, v) <- fields) {
      if (v._2 == 1) {
        namesTranslation += (k -> v._1)
      }
    }
    namesTranslation
  }

  /**
    * Match heap resources to their ast node and translate all identifiers (for fields and references)
    */
  def detHeap(opMapping: Map[Seq[String], String], basicHeap: BasicHeap, program: Program, collections: Set[CEValue], translNames: Map[String, String], model: Model): HeapCounterexample = {
    // choosing all the needed values from the Boogie Model
    var usedIdent = Map[String, Member]()
    for ((key, value) <- opMapping) {
      for (fie <- program.fields) {
        if (key(0) == fie.name || (key(0).startsWith(fie.name ++ "_") && !key.contains("@"))) {
          usedIdent += (value -> fie)
        }
      }
      for (pred <- program.predicates) {
        if (key(0) == pred.name || (key(0).startsWith(pred.name ++ "_") && !key.contains("@"))) {
          usedIdent += (value -> pred)
        }
      }
    }

    var ans = Seq[(Resource, FinalHeapEntry)]()
    for (bhe <- basicHeap.basicHeapEntries) {
      bhe.het match {
        case FieldType | QPFieldType=>
          if (!bhe.perm.isDefined || !(bhe.perm.get == Rational.zero)) {
            usedIdent.get(bhe.field(0)) match {
              case Some(f) =>
                val fi = f.asInstanceOf[Field]
                var found = false
                for (coll <- collections) {
                  if (bhe.valueID == coll.id) {
                    if (translNames.get(bhe.reference.head).isDefined) {
                      ans +:= (fi, FieldFinalEntry(translNames.get(bhe.reference.head).get, fi.name, coll, bhe.perm, fi.typ, bhe.het))
                    } else {
                      ans +:= (fi, FieldFinalEntry(bhe.reference.head, fi.name, coll, bhe.perm, fi.typ, bhe.het))
                    }
                    found = true
                  }
                }
                if (!found) {
                  if (translNames.get(bhe.reference.head).isDefined) {
                    ans +:= (fi, FieldFinalEntry(translNames.get(bhe.reference.head).get, fi.name, CEVariable("#undefined", ConstantEntry(bhe.valueID), Some(fi.typ)), bhe.perm, fi.typ, bhe.het))
                  } else {
                    ans +:= (fi, FieldFinalEntry(bhe.reference.head, fi.name, CEVariable("#undefined", ConstantEntry(bhe.valueID), Some(fi.typ)), bhe.perm, fi.typ, bhe.het))
                  }
                }
              case None => println(s"Could not find a field node for: ${bhe.toString}")
            }
          }
        case PredicateType | QPPredicateType =>
          usedIdent.get(bhe.reference(1)) match {
            case Some(p) =>
              val pr = p.asInstanceOf[Predicate]
              val refNames = bhe.field.map(x =>
                if (translNames.get(x).isDefined) {
                  translNames.get(x).get
                } else {
                  x
                })
              ans +:= (pr, PredFinalEntry(pr.name, refNames, bhe.perm, bhe.insidePredicate, bhe.het))
            case None => println(s"Could not find a predicate node for: ${bhe.toString}")
          }
        case MagicWandType | QPMagicWandType =>
          val translatedArgs = bhe.field.map(x => translNames.getOrElse(x, x))
          for ((mw, idx) <- program.magicWandStructures.zipWithIndex) {
            val mwStructure = mw.structure(program, true)
            val replacements: Iterable[(ast.Node, ast.Node)] = mwStructure.subexpressionsToEvaluate(program).zip(translatedArgs).map(e => e._1 -> ast.LocalVar(e._2, e._1.typ)())
            val repl: scala.collection.immutable.Map[ast.Node, ast.Node] = scala.collection.immutable.Map.from(replacements)
            val transformed = mwStructure.replace(repl)
            if (idx == 0) {
              if (model.entries.get("wand").isDefined && model.entries.get("wand").get.isInstanceOf[MapEntry]) {
                for (s <-  model.entries.get("wand").get.asInstanceOf[MapEntry].options) {
                  if (s._2.toString == bhe.reference(1)) {
                    ans +:= (mw.res(program), WandFinalEntry("wand", transformed.left, transformed.right, scala.collection.immutable.Map[String, String](), bhe.perm, bhe.het))
                  }
                }
              }
            } else {
              val wandName = "wand_" ++ idx.toString
              if (model.entries.get(wandName).isDefined && model.entries.get(wandName).get.isInstanceOf[MapEntry]) {
                for (s <- model.entries.get(wandName).get.asInstanceOf[MapEntry].options) {
                  if (s._2.toString == bhe.reference(1)) {
                    ans +:= (mw, WandFinalEntry(wandName, transformed.left, transformed.right, scala.collection.immutable.Map[String, String](), bhe.perm, bhe.het))
                  }
                }
              }
            }
          }
        case _ => println("This type of heap entry could not be matched correctly!")
      }
    }
    HeapCounterexample(ans)
  }

  def detTranslatedDomains(domEntries: Seq[BasicDomainEntry], namesMap: Map[String, String]) : Seq[BasicDomainEntry] = {
    domEntries.map(de => BasicDomainEntry(de.name, de.types, detTranslatedFunctions(de.functions, namesMap)))
  }

  def detTranslatedFunctions(funEntries: Seq[BasicFunction], namesMap: Map[String, String]) : Seq[BasicFunction] = {
    funEntries.map(bf => detNameTranslationOfFunction(bf, namesMap))
  }

  def detNameTranslationOfFunction(fun: BasicFunction, namesMap: Map[String, String]) : BasicFunction = {
    var tempMap = Map[String, String]()
    for ((k,v) <- namesMap) {
      if (k.startsWith("T@U!val!")) {
        tempMap += (k -> v)
      }
    }
    val translatedFun = fun.options.map { case (in, out) =>
      (in.map(intName => tempMap.getOrElse(intName, intName)), tempMap.getOrElse(out, out))
    }
    val translatedEls = tempMap.getOrElse(fun.default, fun.default)
    BasicFunction(fun.fname, fun.argtypes, fun.returnType, translatedFun, translatedEls)
  }

  def transformInteremdiateCounterexample(e: AbstractError, names: Map[String, Map[String, String]], program: Program, wandNames: Option[Map[MagicWandStructure.MagicWandStructure, Func]]): Unit = {
    if (e.isInstanceOf[VerificationError] && ErrorMemberMapping.mapping.contains(e.asInstanceOf[VerificationError].readableMessage(true, true))) {
      e.asInstanceOf[VerificationError].failureContexts = scala.collection.immutable.Seq(FailureContextImpl(Some(CounterexampleGenerator(e, names, program, wandNames).imCE)))
    }
  }

  def transformExtendedCounterexample(e: AbstractError, names: Map[String, Map[String, String]], program: Program, wandNames: Option[Map[MagicWandStructure.MagicWandStructure, Func]]): Unit = {
    if (e.isInstanceOf[VerificationError] && ErrorMemberMapping.mapping.contains(e.asInstanceOf[VerificationError].readableMessage(true, true))) {
      e.asInstanceOf[VerificationError].failureContexts = scala.collection.immutable.Seq(FailureContextImpl(Some(CounterexampleGenerator(e, names, program, wandNames))))
    }
  }
}