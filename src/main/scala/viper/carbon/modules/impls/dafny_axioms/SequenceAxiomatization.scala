/**
 These axioms are based on the DafnyPrelude.bpl file of Microsoft's Dafny tool.
 See http://dafny.codeplex.com for more information about the Dafny verifier.

 A snapshot of the corresponding DafnyPrelude.bpl file including the date
 of the version and its copyright notices can be found in this directory.

 This file is subject to the terms of the Microsoft Public License
 (Ms-PL). A copy of the Ms-PL is provided in this directory (LICENCE.TXT)
*/

package viper.carbon.modules.impls.dafny_axioms

object SequenceAxiomatization {
  val value = """// START BASICS
                |type Seq T;
                |
                |function Seq#Length<T>(Seq T): int;
                |axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));
                |
                |function Seq#Empty<T>(): Seq T;
                |axiom (forall<T> :: Seq#Length(Seq#Empty(): Seq T) == 0);
                |axiom (forall<T> s: Seq T :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());
                |
                |function Seq#Singleton<T>(T): Seq T;
                |axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);
                |
                |
                |function Seq#Build<T>(s: Seq T, val: T): Seq T;
                |axiom (forall<T> s: Seq T, v: T :: { Seq#Length(Seq#Build(s,v)) }
                |  Seq#Length(Seq#Build(s,v)) == 1 + Seq#Length(s));
                |axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Index(Seq#Build(s,v), i) }
                |  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == v) &&
                |  (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == Seq#Index(s, i)));
                |
                |function Seq#Append<T>(Seq T, Seq T): Seq T;
                |axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
                |s0 != Seq#Empty() && s1 != Seq#Empty() ==>
                |  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));
                |
                |axiom (forall<T> s: Seq T :: { Seq#Append(Seq#Empty(),s) } Seq#Append(Seq#Empty(),s) == s);
                |axiom (forall<T> s: Seq T :: { Seq#Append(s,Seq#Empty()) } Seq#Append(s,Seq#Empty()) == s);
                |
                |function Seq#Index<T>(Seq T, int): T;
                |axiom (forall<T> t: T :: { Seq#Singleton(t) } Seq#Index(Seq#Singleton(t), 0) == t); // AS: changed trigger
                |
                |// END BASICS
                |// START INDEX-APPEND-UPDATE
                |
                |// extra addition function used to force equalities into the e-graph
                |function Seq#Add(int, int) : int;
                |axiom (forall i: int, j: int :: {Seq#Add(i,j)} Seq#Add(i,j) == i + j);
                |function Seq#Sub(int, int) : int;
                |axiom (forall i: int, j: int :: {Seq#Sub(i,j)} Seq#Sub(i,j) == i - j);
                |
                |// AS: split axiom, added constraints
                |axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) } { Seq#Index(s0, n), Seq#Append(s0,s1) } // AS: added alternative trigger
                |  (s0 != Seq#Empty() && s1 != Seq#Empty() && 0 <= n && n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)));
                |axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) } // term below breaks loops
                |  s0 != Seq#Empty() && s1 != Seq#Empty() && Seq#Length(s0) <= n && n < Seq#Length(s0) + Seq#Length(s1) ==> Seq#Add(Seq#Sub(n,Seq#Length(s0)),Seq#Length(s0)) == n && Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, Seq#Sub(n,Seq#Length(s0))));
                |// AS: added "reverse triggering" versions of the axioms
                |axiom (forall<T> s0: Seq T, s1: Seq T, m: int :: { Seq#Index(s1, m), Seq#Append(s0,s1)}  // m == n-|s0|, n == m + |s0|
                |  s0 != Seq#Empty() && s1 != Seq#Empty() && 0 <= m && m < Seq#Length(s1) ==> Seq#Sub(Seq#Add(m,Seq#Length(s0)),Seq#Length(s0)) == m && Seq#Index(Seq#Append(s0,s1), Seq#Add(m,Seq#Length(s0))) == Seq#Index(s1, m));
                |
                |
                |function Seq#Update<T>(Seq T, int, T): Seq T;
                |axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) } {Seq#Length(s),Seq#Update(s,i,v)} // AS: added trigger
                |  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
                |axiom (forall<T> s: Seq T, i: int, v: T, n: int :: { Seq#Index(Seq#Update(s,i,v),n) } { Seq#Index(s,n), Seq#Update(s,i,v) }
                |  0 <= n && n < Seq#Length(s) ==>
                |    (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
                |    (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));
                |
                |// END INDEX-APPEND-UPDATE
                |// START TAKE/DROP
                |
                |function Seq#Take<T>(s: Seq T, howMany: int): Seq T;
                |// AS: added triggers
                |axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) } { Seq#Take(s,n), Seq#Length(s)}
                |  0 <= n ==>
                |    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
                |    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));
                |
                |// ** AS: 2nd of 3 axioms which get instantiated very often in certain problems involving take/drop/append
                |// AS: added triggers
                |axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Take(s,n), j) } {Seq#Index(s,j), Seq#Take(s,n)} // {:weight 25} // AS: dropped weight
                |  0 <= j && j < n && j < Seq#Length(s) ==>
                |    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));
                |
                |function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;
                |axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }{Seq#Length(s), Seq#Drop(s,n)}
                |  0 <= n ==>
                |    (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
                |    (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));
                |
                |// ** AS: 3rd of 3 axioms which get instantiated very often in certain problems involving take/drop/append
                |// split axiom
                |axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) } // {:weight 25} // AS: dropped weight
                |  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
                |   Seq#Sub(Seq#Add(j,n),n) == j && Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, Seq#Add(j,n)));
                |
                |axiom (forall<T> s: Seq T, n: int, i: int :: { Seq#Drop(s,n), Seq#Index(s,i) }
                |  0 <= n && n <= i && i < Seq#Length(s) ==>
                |  Seq#Add(Seq#Sub(i,n),n) == i && Seq#Index(Seq#Drop(s,n), Seq#Sub(i,n)) == Seq#Index(s, i)); // i = j + n, j = i - n
                |
                |// ** AS: We dropped the weak trigger on this axiom. One option is to strengthen the triggers:
                |//axiom (forall<T> s, t: Seq T ::
                | //// { Seq#Append(s, t) }
                |//  {Seq#Take(Seq#Append(s, t), Seq#Length(s))}{Seq#Drop(Seq#Append(s, t), Seq#Length(s))}
                |//  Seq#Take(Seq#Append(s, t), Seq#Length(s)) == s &&
                |//  Seq#Drop(Seq#Append(s, t), Seq#Length(s)) == t);
                |
                |// ** AS: another option is to split the axiom (for some reason, this seems in some cases to perform slightly less well (but this could be random):
                |//axiom (forall<T> s, t: Seq T ::
                |// { Seq#Take(Seq#Append(s, t), Seq#Length(s)) }
                |//  Seq#Take(Seq#Append(s, t), Seq#Length(s)) == s);
                |
                |//axiom (forall<T> s, t: Seq T ::
                |// { Seq#Drop(Seq#Append(s, t), Seq#Length(s)) }
                |//  Seq#Drop(Seq#Append(s, t), Seq#Length(s)) == t);
                |
                |// Commutability of Take and Drop with Update.
                |axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
                |        { Seq#Take(Seq#Update(s, i, v), n) }
                |        0 <= i && i < n && n <= Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );
                |axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
                |        { Seq#Take(Seq#Update(s, i, v), n) }
                |        n <= i && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));
                |axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
                |        { Seq#Drop(Seq#Update(s, i, v), n) }
                |        0 <= n && n <= i && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
                |axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
                |        { Seq#Drop(Seq#Update(s, i, v), n) }
                |        0 <= i && i < n && n < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
                |// drop commutes with build.
                |axiom (forall<T> s: Seq T, v: T, n: int ::
                |        { Seq#Drop(Seq#Build(s, v), n) }
                |        0 <= n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v) );
                |
                |// Additional axioms about common things
                |axiom (forall<T> s: Seq T, n: int :: { Seq#Drop(s, n) } // ** NEW
                |        n <= 0 ==> Seq#Drop(s, n) == s);
                |axiom (forall<T> s: Seq T, n: int :: { Seq#Take(s, n) } // ** NEW
                |        n <= 0 ==> Seq#Take(s, n) == Seq#Empty());
                |axiom (forall<T> s: Seq T, m, n: int :: { Seq#Drop(Seq#Drop(s, m), n) } // ** NEW - AS: could have bad triggering behaviour?
                |        0 <= m && 0 <= n && m+n <= Seq#Length(s) ==>
                |        Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m+n));
                |
                |// END TAKE/DROP
                |
                |// START CONTAINS
                |
                |function Seq#Skolem<T>(Seq T, T) : int; // skolem function for Seq#Contains
                |function Seq#SkolemContainsDrop<T>(Seq T, int, T) : int; // skolem function for Seq#Contains over drop
                |function Seq#SkolemContainsTake<T>(Seq T, int, T) : int; // skolem function for Seq#Contains over take
                |
                |function Seq#Contains<T>(Seq T, T): bool;
                |axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
                |  Seq#Contains(s,x) ==> s != Seq#Empty() && Seq#Length(s) > 0 && 0 <= Seq#Skolem(s,x) &&
                |    Seq#Skolem(s,x) < Seq#Length(s) && Seq#Index(s,Seq#Skolem(s,x)) == x);
                |
                |// AS: note: this is an unusual axiom, but is basically the original
                |// Consider writing a version without the (precise) first trigger? Also see later versions
                |axiom (forall<T> s: Seq T, x: T, i:int :: { Seq#Contains(s,x), Seq#Index(s,i) }
                |  0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x ==> Seq#Contains(s,x));
                |
                |// ** AS: made one change here - changed type of x from ref to T
                |axiom (forall<T> x: T ::
                |  { Seq#Contains(Seq#Empty(), x) }
                |  !Seq#Contains(Seq#Empty(), x));
                |
                |// AS: Consider dropping this axiom?
                |axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
                |  { Seq#Contains(Seq#Append(s0, s1), x) } { Seq#Contains(s0,x), Seq#Append(s0,s1)} { Seq#Contains(s1,x), Seq#Append(s0,s1)} // AS: added triggers
                |  Seq#Contains(Seq#Append(s0, s1), x) <==>
                |    Seq#Contains(s0, x) || Seq#Contains(s1, x));
                |
                |axiom (forall<T> s: Seq T, v: T, x: T ::
                |  { Seq#Contains(Seq#Build(s, v), x) } {Seq#Contains(s,x), Seq#Build(s, v)}
                |    Seq#Contains(Seq#Build(s, v), x) <==> (v == x || Seq#Contains(s, x)));
                |
                |// AS: split axioms
                |axiom (forall<T> s: Seq T, n: int, x: T ::
                |  { Seq#Contains(Seq#Take(s, n), x) }
                |  Seq#Contains(Seq#Take(s, n), x) ==>
                |    (Seq#Take(s, n) != Seq#Empty() && Seq#Length(Seq#Take(s, n)) > 0 &&
                |     0 <= Seq#SkolemContainsTake(s, n, x) && Seq#SkolemContainsTake(s, n, x) < n &&
                |      Seq#SkolemContainsTake(s, n, x) < Seq#Length(s) &&
                |      Seq#Index(s, Seq#SkolemContainsTake(s, n, x)) == x));
                |
                |axiom (forall<T> s: Seq T, n: int, x: T, i:int ::
                |  { Seq#Contains(Seq#Take(s, n), x), Seq#Index(s, i) }
                |    0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x ==>
                |     Seq#Contains(Seq#Take(s, n), x));
                |
                |// AS: split axioms
                |axiom (forall<T> s: Seq T, n: int, x: T ::
                |  { Seq#Contains(Seq#Drop(s, n), x) }
                |  Seq#Contains(Seq#Drop(s, n), x) ==>
                |    ( 0 <= Seq#SkolemContainsDrop(s, n, x) && n <= Seq#SkolemContainsDrop(s, n, x) &&
                |      Seq#SkolemContainsDrop(s, n, x) < Seq#Length(s) &&
                |      Seq#Index(s, Seq#SkolemContainsDrop(s, n, x)) == x));
                |
                |axiom (forall<T> s: Seq T, n: int, x: T, i:int ::
                |  { Seq#Contains(Seq#Drop(s, n), x), Seq#Index(s, i) }
                |  0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x ==>
                |  Seq#Contains(Seq#Drop(s, n), x));
                |
                |// END CONTAINS
                |
                |
                |
                |
                |// START EQUALS
                |
                |function Seq#Equal<T>(Seq T, Seq T): bool;
                |axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
                |  Seq#Equal(s0,s1) <==>
                |    Seq#Length(s0) == Seq#Length(s1) &&
                |    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
                |        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
                |axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
                |  Seq#Equal(a,b) ==> a == b);
                |
                |function Seq#SameUntil<T>(Seq T, Seq T, int): bool;
                |axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#SameUntil(s0,s1,n) }
                |  Seq#SameUntil(s0,s1,n) <==>
                |    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
                |        0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
                |
                |// END EQUALS
                |
                |
                |// START EXTRAS
                |
                |// extra stuff not in current Dafny Prelude
                |
                |axiom (forall<T> x, y: T ::
                |  { Seq#Contains(Seq#Singleton(x),y) }
                |    Seq#Contains(Seq#Singleton(x),y) ==> x==y);
                |
                |axiom (forall<T> x: T ::
                |  { Seq#Singleton(x) }
                |    Seq#Contains(Seq#Singleton(x),x));
                |
                |
                |function Seq#Range(min: int, max: int) returns (Seq int);
                |axiom (forall min: int, max: int :: { Seq#Length(Seq#Range(min, max)) } (min < max ==> Seq#Length(Seq#Range(min, max)) == max-min) && (max <= min ==> Seq#Length(Seq#Range(min, max)) == 0));
                |axiom (forall min: int, max: int, j: int :: { Seq#Index(Seq#Range(min, max), j) } 0<=j && j<max-min ==> Seq#Index(Seq#Range(min, max), j) == min + j);
                |
                |axiom (forall min: int, max: int, v: int :: {Seq#Contains(Seq#Range(min, max),v)}
                |  (Seq#Contains(Seq#Range(min, max),v) <==> min <= v && v < max));
                |
                |// END EXTRAS
                |""".stripMargin
}
