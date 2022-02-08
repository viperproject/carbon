package viper.carbon.utility

import viper.carbon.boogie.{Axiom, Forall, Func, FuncApp, Identifier, LocalVarDecl, NamedType, Namespace, Trigger, Type, TypeVar}

case class MapRep(select: Func, store: Func, axioms: Seq[Axiom])

case class MapDesugarHelper(refType: Type, fieldTypeOf: (Type, Type) => Type, namespace: Namespace) {
  implicit val ns = namespace

  /**
    * Creates store and select functions with corresponding axioms to desugar a Boogie map of the form
    * \code{<...>[ref, Field ...]RangeT}.
    * @param mapRepType               the type that should be used to represent the map type
    * @param selectAndStoreId         the identifiers for selection and store functions
    * @param mapRangeTypeFromField    the range type of the map as an output of the field type
    * @return
    */
  def desugarMap(mapRepType: NamedType,
                 selectAndStoreId: (Identifier, Identifier),
                 mapRangeTypeFromField: Type => Type): MapRep =  {
    val (selectId, storeId) = selectAndStoreId
    val mapTypeId = Identifier(mapRepType.name)
    val h = LocalVarDecl(mapTypeId, mapRepType)
    val obj = LocalVarDecl(Identifier("obj"), refType)
    val obj2 = LocalVarDecl(Identifier("obj2"), refType)
    val field = LocalVarDecl(Identifier("f"), fieldTypeOf(TypeVar("A"), TypeVar("B")))
    val field2 = LocalVarDecl(Identifier("f2"), fieldTypeOf(TypeVar("A2"), TypeVar("B2")))

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

    MapRep(selectFun, storeFun, axioms)
  }
}