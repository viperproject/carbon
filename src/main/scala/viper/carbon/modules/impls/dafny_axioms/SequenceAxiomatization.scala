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
  val value = """type Seq T;
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
      |function Seq#Build<T>(s: Seq T, val: T): Seq T;
      |axiom (forall<T> s: Seq T, v: T :: { Seq#Length(Seq#Build(s,v)) }
      |  Seq#Length(Seq#Build(s,v)) == 1 + Seq#Length(s));
      |axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Index(Seq#Build(s,v), i) }
      |  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == v) &&
      |  (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == Seq#Index(s, i)));
      |
      |function Seq#Append<T>(Seq T, Seq T): Seq T;
      |axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
      |  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));
      |
      |function Seq#Index<T>(Seq T, int): T;
      |axiom (forall<T> t: T :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t);
      |// ** AS: 1st of 3 axioms which get instantiated very often in certain problems involving take/drop/append
      |axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) } // {:weight 25} // AS: dropped weight
      |  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
      |  (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));
      |
      |function Seq#Update<T>(Seq T, int, T): Seq T;
      |axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) }
      |  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
      |axiom (forall<T> s: Seq T, i: int, v: T, n: int :: { Seq#Index(Seq#Update(s,i,v),n) }
      |  0 <= n && n < Seq#Length(s) ==>
      |    (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
      |    (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));
      |
      |function Seq#Contains<T>(Seq T, T): bool;
      |axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
      |  Seq#Contains(s,x) <==>
      |    (exists i: int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x));
      |// ** AS: made one change here - changed type of x from ref to T
      |axiom (forall<T> x: T ::
      |  { Seq#Contains(Seq#Empty(), x) }
      |  !Seq#Contains(Seq#Empty(), x));
      |axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
      |  { Seq#Contains(Seq#Append(s0, s1), x) }
      |  Seq#Contains(Seq#Append(s0, s1), x) <==>
      |    Seq#Contains(s0, x) || Seq#Contains(s1, x));
      |
      |axiom (forall<T> s: Seq T, v: T, x: T ::
      |  { Seq#Contains(Seq#Build(s, v), x) }
      |    Seq#Contains(Seq#Build(s, v), x) <==> (v == x || Seq#Contains(s, x)));
      |
      |axiom (forall<T> s: Seq T, n: int, x: T ::
      |  { Seq#Contains(Seq#Take(s, n), x) }
      |  Seq#Contains(Seq#Take(s, n), x) <==>
      |    (exists i: int :: { Seq#Index(s, i) }
      |      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));
      |axiom (forall<T> s: Seq T, n: int, x: T ::
      |  { Seq#Contains(Seq#Drop(s, n), x) }
      |  Seq#Contains(Seq#Drop(s, n), x) <==>
      |    (exists i: int :: { Seq#Index(s, i) }
      |      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));
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
      |function Seq#Take<T>(s: Seq T, howMany: int): Seq T;
      |axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) }
      |  0 <= n ==>
      |    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
      |    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));
      |// ** AS: 2nd of 3 axioms which get instantiated very often in certain problems involving take/drop/append
      |axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Take(s,n), j) }{ Seq#Index(s, j), Seq#Take(s,n) } // {:weight 25} // AS: dropped weight, added alternative trigger
      |  0 <= j && j < n && j < Seq#Length(s) ==>
      |    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));
      |
      |function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;
      |axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }
      |  0 <= n ==>
      |    (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
      |    (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));
      |// ** AS: 3rd of 3 axioms which get instantiated very often in certain problems involving take/drop/append
      |axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) } // {:weight 25} // AS: dropped weight
      |  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
      |    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));
      |
      |axiom (forall<T> s: Seq T, n: int, k: int :: { Seq#Drop(s,n), Seq#Index(s,k) } // AS: alternative triggering for above axiom
      |  0 <= n && n <= k && k < Seq#Length(s) ==>
      |    Seq#Index(Seq#Drop(s,n), k-n) == Seq#Index(s, k));
      |
      |// ** AS: We dropped the weak trigger on this axiom. One option is to strengthen the triggers:
      |//axiom (forall<T> s, t: Seq T ::
      |// // { Seq#Append(s, t) }
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
      |        n == 0 ==> Seq#Drop(s, n) == s);
      |axiom (forall<T> s: Seq T, n: int :: { Seq#Take(s, n) } // ** NEW
      |        n == 0 ==> Seq#Take(s, n) == Seq#Empty());
      |axiom (forall<T> s: Seq T, m, n: int :: { Seq#Drop(Seq#Drop(s, m), n) } // ** NEW - AS: could have bad triggering behaviour?
      |        0 <= m && 0 <= n && m+n <= Seq#Length(s) ==>
      |        Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m+n));
      |
      |// extra stuff not in current Dafny Prelude -- see also Drop-Index axiom above
      |
      |axiom (forall<T> x, y: T ::
      |  { Seq#Contains(Seq#Singleton(x),y) }
      |    Seq#Contains(Seq#Singleton(x),y) <==> x==y);
      |
      |function Seq#Range(min: int, max: int) returns (Seq int);
      |axiom (forall min: int, max: int :: { Seq#Length(Seq#Range(min, max)) } (min < max ==> Seq#Length(Seq#Range(min, max)) == max-min) && (max <= min ==> Seq#Length(Seq#Range(min, max)) == 0));
      |axiom (forall min: int, max: int, j: int :: { Seq#Index(Seq#Range(min, max), j) } 0<=j && j<max-min ==> Seq#Index(Seq#Range(min, max), j) == min + j);
      |
      |axiom (forall min: int, max: int, v: int :: {Seq#Contains(Seq#Range(min, max),v)}
      |  (Seq#Contains(Seq#Range(min, max),v) <==> min <= v && v < max));
      |
      |
      |""".stripMargin
}
