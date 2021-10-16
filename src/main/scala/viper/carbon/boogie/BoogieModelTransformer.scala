package viper.carbon.boogie

import viper.carbon.verifier.FailureContextImpl
import viper.silver.verifier.{AbstractError, ApplicationEntry, ConstantEntry, Counterexample, ExtractedHeap, FailureContext, FieldHeapEntry, HeapEntry, MapEntry, Model, ModelEntry, PredHeapEntry, Rational, SimpleCounterexample, ValueEntry, VarEntry, VerificationError}
import viper.silver.{ast => sil}

import scala.collection.mutable

/**
  * Transforms a counterexample returned by Boogie back to a Viper counterexample.
  */
object BoogieModelTransformer {

  /**
    * Adds a counterexample to the given error if one is available.
    */
  def transformCounterexample(e: AbstractError, names: Map[String, Map[String, String]], program: sil.Program) : Unit = {
    if (e.isInstanceOf[VerificationError] && ErrorMemberMapping.mapping.contains(e.asInstanceOf[VerificationError])){
      val ve = e.asInstanceOf[VerificationError]
      val methodName = ErrorMemberMapping.mapping.get(ve).get.name
      val namesInMember = names.get(methodName).get.map(e => e._2 -> e._1)
      val originalEntries = ve.failureContexts(0).counterExample.get.model.entries

      val model = transformModelEntries(originalEntries, namesInMember.toMap)

      // TODO: get primary heap and mask
      val primaryMask = getNewestVersion("Mask", ve.failureContexts(0).counterExample.get.model)
      val primaryHeap = getNewestVersion("Heap", ve.failureContexts(0).counterExample.get.model)
      val primaryExtractedHeap = extractHeap(primaryMask, primaryHeap, ve.failureContexts(0).counterExample.get.model, program)

      // TODO: get old heap and mask
      val oldMask = getOldVersion("Mask", ve.failureContexts(0).counterExample.get.model)
      val oldHeap = getOldVersion("Heap", ve.failureContexts(0).counterExample.get.model)
      val oldExtractedHeap = (oldMask, oldHeap) match {
        case (Some(msk), Some(hp)) => Some(extractHeap(msk, hp, ve.failureContexts(0).counterExample.get.model, program))
        case _ => None
      }

      // TODO: get label heaps and masks

      /*
      val maskEntries = getMapEntries(model.entries.get("Mask").get.asInstanceOf[ConstantEntry],  ve.failureContexts(0).counterExample.get.model)
      val realConversion = originalEntries("U_2_real").asInstanceOf[MapEntry]
      val maskEntriesWithPerms: Map[(ValueEntry, ValueEntry), ValueEntry] = maskEntries.map({
        case (k, v) => k -> realConversion.options.get(Seq(v)).get
      })
      val nonZeroMaskEntries = maskEntriesWithPerms.filter(_._2 != ConstantEntry("0.0"))

      val heapEntries = getMapEntries(model.entries.get("Heap").get.asInstanceOf[ConstantEntry],  ve.failureContexts(0).counterExample.get.model)

      val relevantHeapEntries = nonZeroMaskEntries.map({
        case (k, v) if heapEntries.contains(k) => k -> heapEntries.get(k).get
        case (k, v) => k -> ConstantEntry("?")
      })

      println("Store")
      println(model)
      println("Heap")
      nonZeroMaskEntries.foreach({
        case (k, v) if heapEntries.contains(k) => println(s"$k --($v)--> ${heapEntries.get(k).get}")
        case (k, v) => k ->  println(s"$k --($v)--> ?")
      })
      */
      //ve.failureContexts = Seq(FailureContextImpl(Some(SimpleCounterexample(model))))
      ve.failureContexts = Seq(FailureContextImpl(Some(SimpleCounterexample(model))))
    }
  }

  def getOldVersion(varName: String, model: Model): Option[ConstantEntry] = {
    model.entries.find(_._1.startsWith(varName + "@@")).flatMap{case e => Some(e._2.asInstanceOf[ConstantEntry])}
  }

  def getNewestVersion(varName: String, model: Model): ConstantEntry = {
    var highestIndex = -1
    var result: ConstantEntry = null
    model.entries.foreach({
      case (name, entry) if name.startsWith(varName + "@") && name.indexOf("@@") == -1  => {
        val currentIndex = Integer.parseInt(name.substring(name.indexOf("@") + 1))
        if (currentIndex > highestIndex) {
          result = entry.asInstanceOf[ConstantEntry]
          highestIndex = currentIndex
        }
      }
      case _ =>
    })
    result
  }

  def extractHeap(mask: ConstantEntry, heap: ConstantEntry, model: Model, program: sil.Program): ExtractedHeap = {
    val maskEntries = getMapEntries(mask,  model)
    val realConversion = model.entries("U_2_real").asInstanceOf[MapEntry]
    val maskEntriesWithPerms: Map[(ValueEntry, ValueEntry), ValueEntry] = maskEntries.map({
      case (k, v) => k -> realConversion.options.get(Seq(v)).get
    })
    val nonZeroMaskEntries = maskEntriesWithPerms.filter(_._2 != ConstantEntry("0.0"))

    val heapEntries = getMapEntries(heap,  model)

    // get all field and predicate refs
    val fields = new mutable.HashMap[ConstantEntry, sil.Field]()

    val possiblePredicateEntries: Map[MapEntry, sil.Predicate] = model.entries.flatMap{
      case (name, entry) if PrettyPrinter.backMap.contains(name) => {
        val possibleName = PrettyPrinter.backMap.get(name).get
        val possiblePred = program.predicates.find(p => p.name == possibleName)
        if (possiblePred.isDefined) {
          Some(entry.asInstanceOf[MapEntry] -> possiblePred.get)
        }else{
          None
        }
      }
      case _ => None
    }

    val predicates = new mutable.HashMap[ConstantEntry, (sil.Predicate, Seq[ModelEntry])]()

    model.entries.get("IsPredicateField").get.asInstanceOf[MapEntry].options.foreach({
      case (Seq(valEntry), ConstantEntry("false")) => {
        val fieldEntry = model.entries.find({
          case (name, entry) => entry == valEntry && PrettyPrinter.backMap.contains(name)
        })
        println(fieldEntry)
        val origName = PrettyPrinter.backMap.get(fieldEntry.get._1).get
        val field = program.fields.find(_.name == origName).get
        fields.update(fieldEntry.get._2.asInstanceOf[ConstantEntry], field)
      }
      case (Seq(valEntry), ConstantEntry("true")) => {
        for ((entry, pred) <- possiblePredicateEntries) {
          val possibleEntry = entry.options.find(_._2 == valEntry)
          if (possibleEntry.isDefined) {
            predicates.update(valEntry.asInstanceOf[ConstantEntry], (pred, possibleEntry.get._1))
          }
        }
      }
    })
    println(fields)

    val entries: Seq[HeapEntry] = nonZeroMaskEntries.flatMap{
      //case (k, v) if heapEntries.contains(k) => FieldHeapEntry(VarEntry(k._1.toString), "fieldName", None, )//k -> heapEntries.get(k).get
      case ((receiverEntry, fieldEntry), permEntry) => {
        if (fields.contains(fieldEntry.asInstanceOf[ConstantEntry])) {
          val field = fields.get(fieldEntry.asInstanceOf[ConstantEntry]).get
          val perm = convertPermission(permEntry)
          val value = if (heapEntries.contains((receiverEntry, fieldEntry))) {
            VarEntry(heapEntries.get((receiverEntry, fieldEntry)).get.asInstanceOf[ConstantEntry].value)
          } else {
            VarEntry("?")
          }
          Some(FieldHeapEntry(VarEntry(receiverEntry.asInstanceOf[ConstantEntry].value), field.name, Some(perm), value))
        }else{
          val possiblePred = predicates.get(fieldEntry.asInstanceOf[ConstantEntry])
          if (possiblePred.isDefined){
            val pred = possiblePred.get._1
            val args = possiblePred.get._2
            Some(PredHeapEntry(pred.name, args.map(a => VarEntry(a.toString))))
          }else{
            None
          }
        }
      }
    }.toSeq

    // TODO: Convert values, by type
    // TODO: convert perm values
    // TODO:

    /*
    val entries = nonZeroMaskEntries.map({
      case (k, v) if heapEntries.contains(k) => FieldHeapEntry(VarEntry(k._1.toString), "fieldName", None, )//k -> heapEntries.get(k).get
      case (k, v) => //k -> ConstantEntry("?")
    })

    println("Heap")
    nonZeroMaskEntries.foreach({
      case (k, v) if heapEntries.contains(k) => println(s"$k --($v)--> ${heapEntries.get(k).get}")
      case (k, v) => k ->  println(s"$k --($v)--> ?")
    })*/

    ExtractedHeap(entries)
  }

  def convertPermission(value: ValueEntry): Rational = {
    value match {
      case ConstantEntry("1.0") => Rational(1, 1)
      case ConstantEntry("0.0") => Rational(0, 1)
      case ApplicationEntry("/", Seq(ConstantEntry(num), ConstantEntry(dem))) => {
        Rational(num.toDouble.toInt, dem.toDouble.toInt)
      }
    }
  }

  def getMapEntries(mapVal: ConstantEntry, model: Model) : Map[(ValueEntry, ValueEntry), ValueEntry] = {
    val lookupEntries = model.entries.get("[3]").get.asInstanceOf[MapEntry]
    val updateEntries = model.entries.get("[4:=]").get.asInstanceOf[MapEntry]
    val result = new mutable.HashMap[(ValueEntry, ValueEntry), ValueEntry]()
    for ((keys, vl) <- lookupEntries.options) {
      if (keys(0) == mapVal) {
        result.update((keys(1), keys(2)), vl)
      }
    }

    // check if we can recover information from previous versions
    val updateEntry = updateEntries.options.find(_._2 == mapVal)
    if (updateEntry.isDefined) {
      val previousMap = updateEntry.get._1(0).asInstanceOf[ConstantEntry]
      val previousMapEntries = getMapEntries(previousMap, model)
      for ((key, vl) <- previousMapEntries) {
        if (!(key._1 == updateEntry.get._1(1) && key._2 == updateEntry.get._1(2))) {
          result.update(key, vl)
        }
      }
    }
    result.toMap
  }

  /**
    *
    * @param originalEntries Entries of the counterexample produced by Boogie
    * @param namesInMember Mapping from Boogie names to Viper names for the Viper member belonging to this error.
    * @return
    */
  def transformModelEntries(originalEntries: Map[String, ModelEntry], namesInMember: Map[String, String]) : Model = {
    val newEntries = mutable.HashMap[String, ModelEntry]()
    val currentEntryForName = mutable.HashMap[String, String]()
    for ((vname, e) <- originalEntries) {
      var originalName = vname
      if (originalName.startsWith("q@")){
        originalName = originalName.substring(2)
      } else if (originalName.indexOf("@@") != -1){
        originalName = originalName.substring(0, originalName.indexOf("@@"))
      } else if (originalName.indexOf("@") != -1){
        originalName = originalName.substring(0, originalName.indexOf("@"))
      }
      if (PrettyPrinter.backMap.contains(originalName)){
        originalName = PrettyPrinter.backMap.get(originalName).get
        if (namesInMember.contains(originalName)){
          val viperName = namesInMember.get(originalName).get
          if (!currentEntryForName.contains(viperName) ||
            isLaterVersion(vname, originalName, currentEntryForName.get(viperName).get)){
            newEntries.update(viperName, e)
            currentEntryForName.update(viperName, vname)
          }
        }
      }
    }
    Model(newEntries.toMap)
  }

  /**
    * Heuristically (based on Boogie's naming practices) checks if, of the two Boogie versions of the given
    * original Viper variable name, the first denotes a "later" version (as in, occurring later in the program,
    * therefore containing a more recent value).
    */
  def isLaterVersion(firstName: String, originalName: String, secondName: String) : Boolean = {
    if (secondName == originalName || secondName == "q@" + originalName || secondName.indexOf("@@") != -1){
      true
    } else if (secondName.indexOf("@") != -1 && firstName.indexOf("@@") == -1 && firstName.indexOf("@") != -1) {
      val firstIndex = Integer.parseInt(firstName.substring(firstName.indexOf("@") + 1))
      val secondIndex = Integer.parseInt(secondName.substring(secondName.indexOf("@") + 1))
      firstIndex > secondIndex
    } else {
      false
    }
  }
}
