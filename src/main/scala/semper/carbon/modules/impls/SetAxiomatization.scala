package semper.carbon.modules.impls

/**
 * This object contains a set and multiset axiomatization for Boogie.  These axioms have been taken
 * from Dafny (http://dafny.codeplex.com/).  These axioms have been imported on 2013-06-27.
 */
object SetAxiomatization {
  val value =
    """
      |type Set T = [T]bool;
      |
      |function Set#Card<T>(Set T): int;
      |axiom (forall<T> s: Set T :: { Set#Card(s) } 0 <= Set#Card(s));
      |
      |function Set#Empty<T>(): Set T;
      |axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);
      |axiom (forall<T> s: Set T :: { Set#Card(s) }
      |  (Set#Card(s) == 0 <==> s == Set#Empty()) &&
      |  (Set#Card(s) != 0 ==> (exists x: T :: s[x])));
      |
      |function Set#Singleton<T>(T): Set T;
      |axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);
      |axiom (forall<T> r: T, o: T :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);
      |axiom (forall<T> r: T :: { Set#Card(Set#Singleton(r)) } Set#Card(Set#Singleton(r)) == 1);
      |
      |function Set#UnionOne<T>(Set T, T): Set T;
      |axiom (forall<T> a: Set T, x: T, o: T :: { Set#UnionOne(a,x)[o] }
      |  Set#UnionOne(a,x)[o] <==> o == x || a[o]);
      |axiom (forall<T> a: Set T, x: T :: { Set#UnionOne(a, x) }
      |  Set#UnionOne(a, x)[x]);
      |axiom (forall<T> a: Set T, x: T, y: T :: { Set#UnionOne(a, x), a[y] }
      |  a[y] ==> Set#UnionOne(a, x)[y]);
      |axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
      |  a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));
      |axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
      |  !a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);
      |
      |function Set#Union<T>(Set T, Set T): Set T;
      |axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Union(a,b)[o] }
      |  Set#Union(a,b)[o] <==> a[o] || b[o]);
      |axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), a[y] }
      |  a[y] ==> Set#Union(a, b)[y]);
      |axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), b[y] }
      |  b[y] ==> Set#Union(a, b)[y]);
      |axiom (forall<T> a, b: Set T :: { Set#Union(a, b) }
      |  Set#Disjoint(a, b) ==>
      |    Set#Difference(Set#Union(a, b), a) == b &&
      |    Set#Difference(Set#Union(a, b), b) == a);
      |// Follows from the general union axiom, but might be still worth including, because disjoint union is a common case:
      |// axiom (forall<T> a, b: Set T :: { Set#Card(Set#Union(a, b)) }
      |  // Set#Disjoint(a, b) ==>
      |    // Set#Card(Set#Union(a, b)) == Set#Card(a) + Set#Card(b));
      |
      |function Set#Intersection<T>(Set T, Set T): Set T;
      |axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Intersection(a,b)[o] }
      |  Set#Intersection(a,b)[o] <==> a[o] && b[o]);
      |
      |axiom (forall<T> a, b: Set T :: { Set#Union(Set#Union(a, b), b) }
      |  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));
      |axiom (forall<T> a, b: Set T :: { Set#Union(a, Set#Union(a, b)) }
      |  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));
      |axiom (forall<T> a, b: Set T :: { Set#Intersection(Set#Intersection(a, b), b) }
      |  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));
      |axiom (forall<T> a, b: Set T :: { Set#Intersection(a, Set#Intersection(a, b)) }
      |  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));
      |axiom (forall<T> a, b: Set T :: { Set#Card(Set#Union(a, b)) }{ Set#Card(Set#Intersection(a, b)) }
      |  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b)) == Set#Card(a) + Set#Card(b));
      |
      |function Set#Difference<T>(Set T, Set T): Set T;
      |axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Difference(a,b)[o] }
      |  Set#Difference(a,b)[o] <==> a[o] && !b[o]);
      |axiom (forall<T> a, b: Set T, y: T :: { Set#Difference(a, b), b[y] }
      |  b[y] ==> !Set#Difference(a, b)[y] );
      |
      |function Set#Subset<T>(Set T, Set T): bool;
      |axiom(forall<T> a: Set T, b: Set T :: { Set#Subset(a,b) }
      |  Set#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));
      |//axiom(forall<T> a: Set T, b: Set T ::
      |// { Set#Subset(a,b), Set#Card(a), Set#Card(b) }  // very restrictive trigger
      |//  Set#Subset(a,b) ==> Set#Card(a) <= Set#Card(b));
      |
      |
      |function Set#Equal<T>(Set T, Set T): bool;
      |axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }
      |  Set#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));
      |axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }  // extensionality axiom for sets
      |  Set#Equal(a,b) ==> a == b);
      |
      |function Set#Disjoint<T>(Set T, Set T): bool;
      |axiom (forall<T> a: Set T, b: Set T :: { Set#Disjoint(a,b) }
      |  Set#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));
      |
      |// ---------------------------------------------------------------
      |// -- Axiomatization of multisets --------------------------------
      |// ---------------------------------------------------------------
      |
      |function Math#min(a: int, b: int): int;
      |axiom (forall a: int, b: int :: { Math#min(a, b) } a <= b <==> Math#min(a, b) == a);
      |axiom (forall a: int, b: int :: { Math#min(a, b) } b <= a <==> Math#min(a, b) == b);
      |axiom (forall a: int, b: int :: { Math#min(a, b) } Math#min(a, b) == a || Math#min(a, b) == b);
      |
      |function Math#clip(a: int): int;
      |axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);
      |axiom (forall a: int :: { Math#clip(a) } a < 0  ==> Math#clip(a) == 0);
      |
      |type MultiSet T = [T]int;
      |
      |function $IsGoodMultiSet<T>(ms: MultiSet T): bool;
      |// ints are non-negative, used after havocing, and for conversion from sequences to multisets.
      |axiom (forall<T> ms: MultiSet T :: { $IsGoodMultiSet(ms) }
      |  $IsGoodMultiSet(ms) <==> (forall bx: T :: { ms[bx] } 0 <= ms[bx]));
      |
      |function MultiSet#Card<T>(MultiSet T): int;
      |axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));
      |axiom (forall<T> s: MultiSet T, x: T, n: int :: { MultiSet#Card(s[x := n]) }
      |  0 <= n ==> MultiSet#Card(s[x := n]) == MultiSet#Card(s) - s[x] + n);
      |
      |function MultiSet#Empty<T>(): MultiSet T;
      |axiom (forall<T> o: T :: { MultiSet#Empty()[o] } MultiSet#Empty()[o] == 0);
      |axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) }
      |  (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty()) &&
      |  (MultiSet#Card(s) != 0 ==> (exists x: T :: 0 < s[x])));
      |
      |function MultiSet#Singleton<T>(T): MultiSet T;
      |axiom (forall<T> r: T, o: T :: { MultiSet#Singleton(r)[o] } (MultiSet#Singleton(r)[o] == 1 <==> r == o) &&
      |                                                            (MultiSet#Singleton(r)[o] == 0 <==> r != o));
      |axiom (forall<T> r: T :: { MultiSet#Singleton(r) } MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));
      |
      |function MultiSet#UnionOne<T>(MultiSet T, T): MultiSet T;
      |// pure containment axiom (in the original multiset or is the added element)
      |axiom (forall<T> a: MultiSet T, x: T, o: T :: { MultiSet#UnionOne(a,x)[o] }
      |  0 < MultiSet#UnionOne(a,x)[o] <==> o == x || 0 < a[o]);
      |// union-ing increases count by one
      |axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#UnionOne(a, x) }
      |  MultiSet#UnionOne(a, x)[x] == a[x] + 1);
      |// non-decreasing
      |axiom (forall<T> a: MultiSet T, x: T, y: T :: { MultiSet#UnionOne(a, x), a[y] }
      |  0 < a[y] ==> 0 < MultiSet#UnionOne(a, x)[y]);
      |// other elements unchanged
      |axiom (forall<T> a: MultiSet T, x: T, y: T :: { MultiSet#UnionOne(a, x), a[y] }
      |  x != y ==> a[y] == MultiSet#UnionOne(a, x)[y]);
      |axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#Card(MultiSet#UnionOne(a, x)) }
      |  MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);
      |
      |
      |function MultiSet#Union<T>(MultiSet T, MultiSet T): MultiSet T;
      |// union-ing is the sum of the contents
      |axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Union(a,b)[o] }
      |  MultiSet#Union(a,b)[o] == a[o] + b[o]);
      |axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Card(MultiSet#Union(a,b)) }
      |  MultiSet#Card(MultiSet#Union(a,b)) == MultiSet#Card(a) + MultiSet#Card(b));
      |
      |// two containment axioms
      |axiom (forall<T> a, b: MultiSet T, y: T :: { MultiSet#Union(a, b), a[y] }
      |  0 < a[y] ==> 0 < MultiSet#Union(a, b)[y]);
      |axiom (forall<T> a, b: MultiSet T, y: T :: { MultiSet#Union(a, b), b[y] }
      |  0 < b[y] ==> 0 < MultiSet#Union(a, b)[y]);
      |
      |// symmetry axiom
      |axiom (forall<T> a, b: MultiSet T :: { MultiSet#Union(a, b) }
      |  MultiSet#Difference(MultiSet#Union(a, b), a) == b &&
      |  MultiSet#Difference(MultiSet#Union(a, b), b) == a);
      |
      |function MultiSet#Intersection<T>(MultiSet T, MultiSet T): MultiSet T;
      |axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Intersection(a,b)[o] }
      |  MultiSet#Intersection(a,b)[o] == Math#min(a[o],  b[o]));
      |
      |// left and right pseudo-idempotence
      |axiom (forall<T> a, b: MultiSet T :: { MultiSet#Intersection(MultiSet#Intersection(a, b), b) }
      |  MultiSet#Intersection(MultiSet#Intersection(a, b), b) == MultiSet#Intersection(a, b));
      |axiom (forall<T> a, b: MultiSet T :: { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) }
      |  MultiSet#Intersection(a, MultiSet#Intersection(a, b)) == MultiSet#Intersection(a, b));
      |
      |// multiset difference, a - b. clip() makes it positive.
      |function MultiSet#Difference<T>(MultiSet T, MultiSet T): MultiSet T;
      |axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Difference(a,b)[o] }
      |  MultiSet#Difference(a,b)[o] == Math#clip(a[o] - b[o]));
      |axiom (forall<T> a, b: MultiSet T, y: T :: { MultiSet#Difference(a, b), b[y], a[y] }
      |  a[y] <= b[y] ==> MultiSet#Difference(a, b)[y] == 0 );
      |
      |// multiset subset means a must have at most as many of each element as b
      |function MultiSet#Subset<T>(MultiSet T, MultiSet T): bool;
      |axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Subset(a,b) }
      |  MultiSet#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <= b[o]));
      |
      |function MultiSet#Equal<T>(MultiSet T, MultiSet T): bool;
      |axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
      |  MultiSet#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == b[o]));
      |// extensionality axiom for multisets
      |axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
      |  MultiSet#Equal(a,b) ==> a == b);
      |
      |function MultiSet#Disjoint<T>(MultiSet T, MultiSet T): bool;
      |axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Disjoint(a,b) }
      |  MultiSet#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == 0 || b[o] == 0));
      |
      |// conversion to a multiset. each element in the original set has duplicity 1.
      |function MultiSet#FromSet<T>(Set T): MultiSet T;
      |axiom (forall<T> s: Set T, a: T :: { MultiSet#FromSet(s)[a] }
      |  (MultiSet#FromSet(s)[a] == 0 <==> !s[a]) &&
      |  (MultiSet#FromSet(s)[a] == 1 <==> s[a]));
      |axiom (forall<T> s: Set T :: { MultiSet#Card(MultiSet#FromSet(s)) }
      |  MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));
      |
      |// conversion to a multiset, from a sequence.
      |function MultiSet#FromSeq<T>(Seq T): MultiSet T;
      |// conversion produces a good map.
      |axiom (forall<T> s: Seq T :: { MultiSet#FromSeq(s) } $IsGoodMultiSet(MultiSet#FromSeq(s)) );
      |// building axiom
      |axiom (forall<T> s: Seq T, v: T ::
      |  { MultiSet#FromSeq(Seq#Build(s, v)) }
      |    MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v)
      |  );
      |axiom (forall<T> :: MultiSet#FromSeq(Seq#Empty(): Seq T) == MultiSet#Empty(): MultiSet T);
      |
      |// concatenation axiom
      |axiom (forall<T> a: Seq T, b: Seq T ::
      |  { MultiSet#FromSeq(Seq#Append(a, b)) }
      |    MultiSet#FromSeq(Seq#Append(a, b)) == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)) );
      |
      |// update axiom
      |axiom (forall<T> s: Seq T, i: int, v: T, x: T ::
      |  { MultiSet#FromSeq(Seq#Update(s, i, v))[x] }
      |    0 <= i && i < Seq#Length(s) ==>
      |    MultiSet#FromSeq(Seq#Update(s, i, v))[x] ==
      |      MultiSet#Union(MultiSet#Difference(MultiSet#FromSeq(s), MultiSet#Singleton(Seq#Index(s,i))), MultiSet#Singleton(v))[x] );
      |  // i.e. MS(Update(s, i, v)) == MS(s) - {{s[i]}} + {{v}}
      |axiom (forall<T> s: Seq T, x: T :: { MultiSet#FromSeq(s)[x] }
      |  (exists i : int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && x == Seq#Index(s,i)) <==> 0 < MultiSet#FromSeq(s)[x] );
    """.stripMargin
}
