package viper.carbon.utility

import viper.carbon.boogie.{Axiom, Forall, Func, FuncApp, Identifier, LocalVarDecl, NamedType, Namespace, Trigger, Type, TypeVar}

/**
  * Representation of desugared version of polymorphic type
  * @param select Boogie function for map lookups
  * @param store Boogie function for map stores
  * @param axioms axioms constraining the select and store functions
  */
case class PolyMapRep(select: Func, store: Func, axioms: Seq[Axiom])

/***
  *  Class that can desugar a specific category of polymorphic Boogie maps, namely Boogie maps of the form
  *  {@code <...>[ref, Field ...]RangeType} where \code{ref} is type representing references (no type arguments),
  *  {@code Field} is a type constructor representing fields.
  * @param refType type representing references
  * @param fieldTypeConstructor [[fieldTypeConstructor._2]] constructs a field type given [[fieldTypeConstructor._1]] type arguments
  * @param namespace
  */
case class PolyMapDesugarHelper(refType: Type, fieldTypeConstructor: (Int, Seq[Type] => Type), namespace: Namespace) {
  implicit val ns = namespace

  /**
    * Creates store and select functions with corresponding axioms to desugar a Boogie map of the form
    * {@code <...>[ref, Field ... ...]RangeType} .
    * @param mapRepType               the type that should be used to represent the map type
    * @param selectAndStoreId         the identifiers for selection and store functions
    * @param mapRangeTypeFromField    the range type of the map as a function of the field type
    * @return [[PolyMapRep]] representation of desugared type
    */
  def desugarPolyMap(mapRepType: NamedType,
                     selectAndStoreId: (Identifier, Identifier),
                     mapRangeTypeFromField: Type => Type): PolyMapRep =  {
    val (selectId, storeId) = selectAndStoreId
    val mapTypeId = Identifier(mapRepType.name)
    val h = LocalVarDecl(mapTypeId, mapRepType)
    val obj = LocalVarDecl(Identifier("obj"), refType)
    val obj2 = LocalVarDecl(Identifier("obj2"), refType)

    val field = LocalVarDecl(Identifier("f"),
                  fieldTypeConstructor._2(Seq.tabulate(fieldTypeConstructor._1){ i => TypeVar("A"+i) }))
    val field2 = LocalVarDecl(Identifier("f2"),
                  fieldTypeConstructor._2(Seq.tabulate(fieldTypeConstructor._1){ i => TypeVar("B"+i) }))

    val selectFun =
      Func(selectId,
        Seq(h, obj, field),
        mapRangeTypeFromField(field.typ))

    val storeFun =
      Func(storeId,
        Seq(h, obj, field, LocalVarDecl(Identifier("y"), mapRangeTypeFromField(field.typ))),
        mapRepType)

    val declInHeapRange = LocalVarDecl(Identifier("y"), mapRangeTypeFromField(field.typ))
    val readUpdateGeneral =
      FuncApp(selectId,
        Seq(FuncApp(storeId, Seq(h.l, obj.l, field.l, declInHeapRange.l), mapRepType), obj2.l, field2.l),
        mapRangeTypeFromField(field2.typ)
      )
    val axioms =
      Seq(
        Axiom(Forall(
          Seq(h,obj,field,declInHeapRange),
          Seq(Trigger(Seq(FuncApp(storeId, Seq(h.l, obj.l, field.l, declInHeapRange.l), mapRepType)))),
          FuncApp(selectId,
            Seq(FuncApp(storeId, Seq(h.l, obj.l, field.l, declInHeapRange.l), mapRepType), obj.l, field.l),
            mapRangeTypeFromField(field.typ)
          ) === declInHeapRange.l
        )),
          Axiom(Forall(
            Seq(h,obj,obj2, field,field2, declInHeapRange),
            Seq(Trigger(Seq(readUpdateGeneral))),
            ( (obj.l !== obj2.l) || (field.l !== field2.l) ) ==>
              ( readUpdateGeneral === FuncApp(selectId, Seq(h.l, obj2.l, field2.l),
                mapRangeTypeFromField(field2.typ) ) )
          )))

    PolyMapRep(selectFun, storeFun, axioms)
  }
}