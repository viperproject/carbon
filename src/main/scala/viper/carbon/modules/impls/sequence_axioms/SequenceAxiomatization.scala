// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

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
  val value = """ // diff 0 implemented (no difference)
                | // diff 1 implemented (fixes test5 in sequences.sil)
                | // diff 2 implemented (fixes m01 and m03 in quantifiedpermissions/issues/issue_0064)
                | // diff 3 implemented (no difference)
                | // diff 4 implemented (no difference)
                | // diff 5 implemented (fixes colourings0 in sequence-incompletenesses test case)
                | // diff 6 implemented (no difference)
                | // diff 7 implemented
                | // diff 8 implemented (allows for contains triggering, without destroying performance of e.g. functions/linkedlists test case)
                | // diff 11 implemented
                | // diff 13 implemented, for now (may reduce completeness, but there's a known matching loop when the first drop amount is 0); another option would be to add !=0 as an explicit condition
                | // diff 14 implemented: eliminate index over take/drop for trivial cases (to avoid matching loops when e.g. s[i..] == s is known)
                | // diff 16 implemented: remove general cases of equality-learning between take/drop/append subsequences; only allow when take/drop are at top level (this affects linkedlists test case)
                |// START BASICS
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
                |//axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);// (diff 2 (old))
                |axiom (forall<T> t: T :: { Seq#Singleton(t) } Seq#Length(Seq#Singleton(t)) == 1);// (diff 2: changed trigger)
                |
                |function Seq#Append<T>(Seq T, Seq T): Seq T;
                |axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
                |s0 != Seq#Empty() && s1 != Seq#Empty() ==> //diff 11: consider removing constraints
                |  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));
                |
                |//axiom (forall<T> s: Seq T :: { Seq#Append(Seq#Empty(),s) } Seq#Append(Seq#Empty(),s) == s); // (diff 11: switched to double-quantified version)
                |//axiom (forall<T> s: Seq T :: { Seq#Append(s,Seq#Empty()) } Seq#Append(s,Seq#Empty()) == s); // (diff 11: switched to double-quantified version)
                |axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Append(s0,s1) } (s0 == Seq#Empty() ==> Seq#Append(s0,s1) == s1) && (s1 == Seq#Empty() ==> Seq#Append(s0,s1) == s0)); // diff 11: switched to double-quantified version
                |
                |function Seq#Index<T>(Seq T, int): T;
                |//axiom (forall<T> t: T :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t); // (diff 2 (old))
                |axiom (forall<T> t: T :: { Seq#Singleton(t) } Seq#Index(Seq#Singleton(t), 0) == t); // (diff 2: changed trigger)
                |
                |// END BASICS
                |
                |// START INDEX-APPEND-UPDATE
                |
                |// extra addition function used to force equalities into the e-graph
                |function Seq#Add(int, int) : int;
                |axiom (forall i: int, j: int :: {Seq#Add(i,j)} Seq#Add(i,j) == i + j);
                |function Seq#Sub(int, int) : int;
                |axiom (forall i: int, j: int :: {Seq#Sub(i,j)} Seq#Sub(i,j) == i - j);
                |
                |// (diff 3 (old))
                |//axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) } // {:weight 25} // AS: dropped weight
                |//  s0 != Seq#Empty() && s1 != Seq#Empty() ==>
                |//  ((n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
                |//  (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0)))));
                |
                |// (diff 3: split axiom, added constraints, replace arithmetic) // diff 11: consider removing constraints
                |axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) } { Seq#Index(s0, n), Seq#Append(s0,s1) } // AS: added alternative trigger
                |  (s0 != Seq#Empty() && s1 != Seq#Empty() && 0 <= n && n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)));
                |axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) } // term below breaks loops
                |  s0 != Seq#Empty() && s1 != Seq#Empty() && Seq#Length(s0) <= n && n < Seq#Length(Seq#Append(s0,s1)) ==> Seq#Add(Seq#Sub(n,Seq#Length(s0)),Seq#Length(s0)) == n && Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, Seq#Sub(n,Seq#Length(s0))));
                |// AS: added "reverse triggering" versions of the axioms
                |axiom (forall<T> s0: Seq T, s1: Seq T, m: int :: { Seq#Index(s1, m), Seq#Append(s0,s1)}  // m == n-|s0|, n == m + |s0|
                |  s0 != Seq#Empty() && s1 != Seq#Empty() && 0 <= m && m < Seq#Length(s1) ==> Seq#Sub(Seq#Add(m,Seq#Length(s0)),Seq#Length(s0)) == m && Seq#Index(Seq#Append(s0,s1), Seq#Add(m,Seq#Length(s0))) == Seq#Index(s1, m));
                |
                |function Seq#Update<T>(Seq T, int, T): Seq T;
                |axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) } {Seq#Length(s),Seq#Update(s,i,v)} // (diff 4: added trigger)
                |  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
                |axiom (forall<T> s: Seq T, i: int, v: T, n: int :: { Seq#Index(Seq#Update(s,i,v),n) } { Seq#Index(s,n), Seq#Update(s,i,v) }  // (diff 4: added trigger)
                |  0 <= n && n < Seq#Length(s) ==>
                |    (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
                |    (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));
                |
                |// END INDEX-APPEND-UPDATE
                |
                |// START TAKE/DROP
                |
                |function Seq#Take<T>(s: Seq T, howMany: int): Seq T;
                |// AS: added triggers
                |axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) } { Seq#Take(s,n), Seq#Length(s)} // (diff 7: add trigger)
                |  (0 <= n ==>
                |    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
                |    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)))
                |    &&
                |   (n < 0 ==> Seq#Length(Seq#Take(s,n)) == 0)); // (diff 7: added case for n < 0)
                |
                |// ** AS: 2nd of 3 axioms which get instantiated very often in certain problems involving take/drop/append
                |axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Take(s,n), j) } {Seq#Index(s,j), Seq#Take(s,n)} // (diff 0: (was already done)) : add trigger // {:weight 25} // AS: dropped weight
                |  0 <= j && j < n && j < Seq#Length(s) ==>
                |    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));
                |
                |function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;
                |axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) } {Seq#Length(s), Seq#Drop(s,n)} // (diff 5: added trigger, exchange arithmetic)
                |  (0 <= n ==>
                |    (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
                |    (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0))
                |    &&
                |  (n < 0 ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s)) // (diff 7: added cases for n < 0)
                |    );
                |
                |// ** AS: 3rd of 3 axioms which get instantiated very often in certain problems involving take/drop/append
                |// diff 5 (old)
                |//axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) } // {:weight 25} // AS: dropped weight
                |//  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
                |//    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));
                |//
                |// diff already added // diff -1: try removing this axiom and checking effect
                |//axiom (forall<T> s: Seq T, n: int, k: int :: { Seq#Drop(s,n), Seq#Index(s,k) } // AS: alternative triggering for above axiom
                |//  0 <= n && n <= k && k < Seq#Length(s) ==>
                |//    Seq#Index(Seq#Drop(s,n), k-n) == Seq#Index(s, k));
                |
                |// diff 5: split axiom, added triggering case, exhanged arithmetic
                |
                |axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) } // {:weight 25} // AS: dropped weight
                |  0 < n && 0 <= j && j < Seq#Length(s)-n ==> // diff 14: change 0 <= n to 0 < n
                |   Seq#Sub(Seq#Add(j,n),n) == j && Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, Seq#Add(j,n)));
                |
                |axiom (forall<T> s: Seq T, n: int, i: int :: { Seq#Drop(s,n), Seq#Index(s,i) }
                |  0 < n && n <= i && i < Seq#Length(s) ==> // diff 14: change 0 <= n to 0 < n
                |  Seq#Add(Seq#Sub(i,n),n) == i && Seq#Index(Seq#Drop(s,n), Seq#Sub(i,n)) == Seq#Index(s, i)); // i = j + n, j = i - n
                |
                |// (diff 6a: add axioms for the 0 > n case)
                |//axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) } // {:weight 25} // AS: dropped weight
                |//  n <= 0 && 0 <= j && j < Seq#Length(s) ==> // diff 14: change n < 0 to n <= 0
                |//    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j));
                |
                |// (diff 6a: add axioms for the 0 > n case)
                |//axiom (forall<T> s: Seq T, n: int, i: int :: { Seq#Drop(s,n), Seq#Index(s,i) }
                |//  n <= 0 && 0 <= i && i < Seq#Length(s) ==> // diff 14: change n < 0 to n <= 0
                |//  Seq#Index(Seq#Drop(s,n), i) == Seq#Index(s, i)); // i = j + n, j = i - n
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
                |// (diff 6b: remove these?)
                |/* Removed: at present, Carbon doesn't generate Seq#Update (but desugars via take/drop/append)
                |// Commutability of Take and Drop with Update.
                |axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
                |        { Seq#Take(Seq#Update(s, i, v), n) }
                |//        0 <= i && i < n && n < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );
                |        0 <= i && i < n && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );
                |axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
                |        { Seq#Take(Seq#Update(s, i, v), n) }
                |        n <= i && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));
                |axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
                |        { Seq#Drop(Seq#Update(s, i, v), n) }
                |//        0 <= n && n <= i && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
                |        0 <= i && n <=i && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
                |axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
                |        { Seq#Drop(Seq#Update(s, i, v), n) }
                |//        0 <= i && i < n && n < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
                |        0 <= i && i < n && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
                |*/
                |
                |axiom (forall<T> s: Seq T, t: Seq T, n:int ::
                |  { Seq#Take(Seq#Append(s,t),n) } //{Seq#Append(s,t), Seq#Take(s,n)} // diff 16: temporarily dropped general case of these
                |  0 < n && n <= Seq#Length(s) ==> Seq#Take(Seq#Append(s,t),n) == Seq#Take(s,n));
                |
                |axiom (forall<T> s: Seq T, t: Seq T, n:int ::
                |  { Seq#Take(Seq#Append(s,t),n) }
                |  n > 0 && n > Seq#Length(s) ==> Seq#Add(Seq#Sub(n,Seq#Length(s)),Seq#Length(s)) == n && Seq#Take(Seq#Append(s,t),n) == Seq#Append(s,Seq#Take(t,Seq#Sub(n,Seq#Length(s)))));
                |
                |// diff 16: temporarily dropped general case of these
                |//axiom (forall<T> s: Seq T, t: Seq T, m:int ::
                |//  { Seq#Append(s,Seq#Take(t,m)) } //{Seq#Append(s,t), Seq#Take(t,m)} // diff 16: temporarily dropped general case of these // reverse triggering version of above: m = n - |s|, n = m + |s|
                |//  m > 0 ==> Seq#Sub(Seq#Add(m,Seq#Length(s)),Seq#Length(s)) == m && Seq#Take(Seq#Append(s,t),Seq#Add(m,Seq#Length(s))) == Seq#Append(s,Seq#Take(t,m)));
                |
                |axiom (forall<T> s: Seq T, t: Seq T, n:int ::
                |  { Seq#Drop(Seq#Append(s,t),n) } //{Seq#Append(s,t), Seq#Drop(s,n)} // diff 16: temporarily dropped general case of these
                |  0<n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Append(s,t),n) == Seq#Append(Seq#Drop(s,n),t));
                |
                |axiom (forall<T> s: Seq T, t: Seq T, n:int ::
                |  { Seq#Drop(Seq#Append(s,t),n) }
                | n > 0 && n > Seq#Length(s) ==> Seq#Add(Seq#Sub(n,Seq#Length(s)),Seq#Length(s)) == n && Seq#Drop(Seq#Append(s,t),n) == Seq#Drop(t,Seq#Sub(n,Seq#Length(s))));
                |
                |// diff 16: temporarily dropped general case of these
                |//axiom (forall<T> s: Seq T, t: Seq T, m:int ::
                |//  { Seq#Append(s,t),Seq#Drop(t,m) } // reverse triggering version of above: m = n - |s|, n = m + |s|
                |//  m > 0 ==> Seq#Sub(Seq#Add(m,Seq#Length(s)),Seq#Length(s)) == m && Seq#Drop(Seq#Append(s,t),Seq#Add(m,Seq#Length(s))) == Seq#Drop(t,m));
                |
                |// Additional axioms about common things
                |axiom (forall<T> s: Seq T, n: int :: { Seq#Drop(s, n) } // ** NEW
                |        n <= 0 ==> Seq#Drop(s, n) == s); // (diff 1: try changing n==0 to n<=0 (should be ok))
                |axiom (forall<T> s: Seq T, n: int :: { Seq#Take(s, n) } // ** NEW
                |        n <= 0 ==> Seq#Take(s, n) == Seq#Empty());  // (diff 1: try changing n==0 to n<=0 (should be ok))
                |// diff 13: remove this?
                |//axiom (forall<T> s: Seq T, m, n: int :: { Seq#Drop(Seq#Drop(s, m), n) } // ** NEW - AS: could have bad triggering behaviour?
                |//        0 <= m && 0 <= n && m+n <= Seq#Length(s) ==>
                |//        Seq#Sub(Seq#Add(m,n),n) == m && Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, Seq#Add(m,n)));
                |
                |// END TAKE/DROP
                |
                |// START CONTAINS
                |// diff 8: skolemisation (old)
                |function Seq#Contains<T>(Seq T, T): bool;
                |function Seq#ContainsTrigger<T>(Seq T, T): bool; // usages of Contains inside quantifier triggers are replaced with this
                |function Seq#Skolem<T>(Seq T, T) : int; // skolem function for Seq#Contains // (diff 8: added)
                |axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
                |  Seq#Contains(s,x) ==>
                |    (0 <= Seq#Skolem(s,x) && Seq#Skolem(s,x) < Seq#Length(s) && Seq#Index(s,Seq#Skolem(s,x)) == x)); // (diff 8: skolem function)
                |axiom (forall<T> s: Seq T, x: T, i:int :: { Seq#Contains(s,x), Seq#Index(s,i) } // only trigger if interested in the Contains term
                |    (0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x ==> Seq#Contains(s,x)));
                |axiom (forall<T> s: Seq T, i:int :: { Seq#Index(s,i) }
                |  (0 <= i && i < Seq#Length(s) ==> Seq#ContainsTrigger(s,Seq#Index(s,i))));
                |// ** AS: made one change here - changed type of x from ref to T
                |/*axiom (forall<T> x: T ::
                |  { Seq#Contains(Seq#Empty(), x) }
                |  !Seq#Contains(Seq#Empty(), x));
                |axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
                |  { Seq#Contains(Seq#Append(s0, s1), x) }
                |  Seq#Contains(Seq#Append(s0, s1), x) <==>
                |    Seq#Contains(s0, x) || Seq#Contains(s1, x));
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
                |*/
                |// diff 8: skolemisation (new)
                |/*
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
                |*/
                |
                |// END CONTAINS
                |
                |// START EQUALS
                |
                |// diff 9 : skolemise equals (old)
                |function Seq#Equal<T>(Seq T, Seq T): bool;
                |/*axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
                |  Seq#Equal(s0,s1) <==>
                |    Seq#Length(s0) == Seq#Length(s1) &&
                |    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
                |        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
                |
                |axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
                |  Seq#Equal(a,b) ==> a == b);
                |*/
                |// diff 9: skolemise equals (new)
                |// AS: split axiom
                |axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
                |  Seq#Equal(s0,s1) ==>
                |    Seq#Length(s0) == Seq#Length(s1) &&
                |    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
                |        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
                |
                |function Seq#SkolemDiff<T>(Seq T, Seq T) : int; // skolem function for Seq#Equals
                |
                |axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
                |  (s0==s1 && Seq#Equal(s0,s1)) || (s0!=s1 && !Seq#Equal(s0,s1) && Seq#Length(s0) != Seq#Length(s1)) ||
                |        (s0 != s1 && !Seq#Equal(s0,s1) && Seq#Length(s0) == Seq#Length(s1) && Seq#SkolemDiff(s0,s1) == Seq#SkolemDiff(s1,s0) && 0 <= Seq#SkolemDiff(s0,s1) && Seq#SkolemDiff(s0,s1) < Seq#Length(s0) &&
                |         Seq#Index(s0,Seq#SkolemDiff(s0,s1)) != Seq#Index(s1,Seq#SkolemDiff(s0,s1))));
                |
                |axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
                |  Seq#Equal(a,b) ==> a == b);
                |
                |
                |// END EQUALS
                |
                |
                |// START EXTRAS
                |
                |// extra stuff not in current Dafny Prelude
                |
                |// diff 10: variant of trigger (maybe drop these?)
                |// old:
                |axiom (forall<T> x, y: T ::
                |  { Seq#Contains(Seq#Singleton(x),y) }
                |    Seq#Contains(Seq#Singleton(x),y) <==> x==y);
                |// new:
                |/*axiom (forall<T> x, y: T ::
                |  { Seq#Contains(Seq#Singleton(x),y) }
                |    Seq#Contains(Seq#Singleton(x),y) ==> x==y);
                |
                |axiom (forall<T> x: T ::
                |  { Seq#Singleton(x) }
                |    Seq#Contains(Seq#Singleton(x),x));
                |*/
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
