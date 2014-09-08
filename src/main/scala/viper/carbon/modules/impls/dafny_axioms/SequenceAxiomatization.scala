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
  val value = """type Seq_ T;
                |
                |function Seq#Length<T>(Seq_ T): int;
                |axiom (forall<T> s: Seq_ T :: { Seq#Length(s) } 0 <= Seq#Length(s));
                |
                |function Seq#Empty<T>(): Seq_ T;
                |axiom (forall<T> :: Seq#Length(Seq#Empty(): Seq_ T) == 0);
                |axiom (forall<T> s: Seq_ T :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());
                |
                |function Seq#Singleton<T>(T): Seq_ T;
                |axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);
                |
                |function Seq#Append<T>(Seq_ T, Seq_ T): Seq_ T;
                |axiom (forall<T> s0: Seq_ T, s1: Seq_ T :: { Seq#Length(Seq#Append(s0,s1)) }
                |  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));
                |
                |function Seq#Index<T>(Seq_ T, int): T;
                |axiom (forall<T> t: T :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t);
                |axiom (forall<T> s0: Seq_ T, s1: Seq_ T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
                |  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
                |  (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));
                |
                |function Seq#Update<T>(Seq_ T, int, T): Seq_ T;
                |axiom (forall<T> s: Seq_ T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) }
                |  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
                |axiom (forall<T> s: Seq_ T, i: int, v: T, n: int :: { Seq#Index(Seq#Update(s,i,v),n) }
                |  0 <= n && n < Seq#Length(s) ==>
                |    (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
                |    (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));
                |
                |function Seq#Contains<T>(Seq_ T, T): bool;
                |axiom (forall<T> s: Seq_ T, x: T :: { Seq#Contains(s,x) }
                |  Seq#Contains(s,x) <==>
                |    (exists i: int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x));
                |axiom (forall x: Ref ::
                |  { Seq#Contains(Seq#Empty(), x) }
                |  !Seq#Contains(Seq#Empty(), x));
                |axiom (forall<T> s0: Seq_ T, s1: Seq_ T, x: T ::
                |  { Seq#Contains(Seq#Append(s0, s1), x) }
                |  Seq#Contains(Seq#Append(s0, s1), x) <==>
                |    Seq#Contains(s0, x) || Seq#Contains(s1, x));
                |
                |axiom (forall<T> s: Seq_ T, n: int, x: T ::
                |  { Seq#Contains(Seq#Take(s, n), x) }
                |  Seq#Contains(Seq#Take(s, n), x) <==>
                |    (exists i: int :: { Seq#Index(s, i) }
                |      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));
                |axiom (forall<T> s: Seq_ T, n: int, x: T ::
                |  { Seq#Contains(Seq#Drop(s, n), x) }
                |  Seq#Contains(Seq#Drop(s, n), x) <==>
                |    (exists i: int :: { Seq#Index(s, i) }
                |      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));
                |
                |function Seq#Equal<T>(Seq_ T, Seq_ T): bool;
                |axiom (forall<T> s0: Seq_ T, s1: Seq_ T :: { Seq#Equal(s0,s1) }
                |  Seq#Equal(s0,s1) <==>
                |    Seq#Length(s0) == Seq#Length(s1) &&
                |    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
                |        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
                |axiom (forall<T> a: Seq_ T, b: Seq_ T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
                |  Seq#Equal(a,b) ==> a == b);
                |
                |function Seq#Take<T>(s: Seq_ T, howMany: int): Seq_ T;
                |axiom (forall<T> s: Seq_ T, n: int :: { Seq#Length(Seq#Take(s,n)) }
                |  0 <= n ==>
                |    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
                |    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));
                |axiom (forall<T> s: Seq_ T, n: int, j: int :: { Seq#Index(Seq#Take(s,n), j) } {:weight 25}
                |  0 <= j && j < n && j < Seq#Length(s) ==>
                |    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));
                |
                |function Seq#Drop<T>(s: Seq_ T, howMany: int): Seq_ T;
                |axiom (forall<T> s: Seq_ T, n: int :: { Seq#Length(Seq#Drop(s,n)) }
                |  0 <= n ==>
                |    (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
                |    (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));
                |axiom (forall<T> s: Seq_ T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) } {:weight 25}
                |  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
                |    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));
                |
                |axiom (forall<T> s, t: Seq_ T ::
                |  { Seq#Append(s, t) }
                |  Seq#Take(Seq#Append(s, t), Seq#Length(s)) == s &&
                |  Seq#Drop(Seq#Append(s, t), Seq#Length(s)) == t);
                |
                |// Commutability of Take and Drop with Update.
                |axiom (forall<T> s: Seq_ T, i: int, v: T, n: int ::
                |  { Seq#Take(Seq#Update(s, i, v), n) }
                |    0 <= i && i < n && n <= Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );
                |axiom (forall<T> s: Seq_ T, i: int, v: T, n: int ::
                |  { Seq#Take(Seq#Update(s, i, v), n) }
                |    n <= i && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));
                |axiom (forall<T> s: Seq_ T, i: int, v: T, n: int ::
                |  { Seq#Drop(Seq#Update(s, i, v), n) }
                |    0 <= n && n <= i && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
                |axiom (forall<T> s: Seq_ T, i: int, v: T, n: int ::
                |  { Seq#Drop(Seq#Update(s, i, v), n) }
                |    0 <= i && i < n && n < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
                |
                |function Seq#Range(min: int, max: int) returns (Seq_ int);
                |
                |axiom (forall min: int, max: int :: { Seq#Length(Seq#Range(min, max)) } (min < max ==> Seq#Length(Seq#Range(min, max)) == max-min) && (max <= min ==> Seq#Length(Seq#Range(min, max)) == 0));
                |axiom (forall min: int, max: int, j: int :: { Seq#Index(Seq#Range(min, max), j) } 0<=j && j<max-min ==> Seq#Index(Seq#Range(min, max), j) == min + j);
                |
                |axiom (forall<T> x, y: T ::
                |  { Seq#Contains(Seq#Singleton(x),y) }
                |    Seq#Contains(Seq#Singleton(x),y) <==> x==y);
                |
                |axiom (forall min: int, max: int, v: int :: {Seq#Contains(Seq#Range(min, max),v)}
                |  (Seq#Contains(Seq#Range(min, max),v) <==> min <= v && v < max));
                |
                |""".stripMargin
}
