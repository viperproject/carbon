package viper.carbon.modules.impls.sequence_axioms

object SiliconSequenceAxiomatization {
  val value =
    """
      |type Seq T;
      |
      |function Seq#Length<T>(Seq T): int;
      |function Seq#Empty<T>(): Seq T;
      |function Seq#Singleton<T>(T): Seq T;
      |function Seq#Build<T>(Seq T, T): Seq T;
      |function Seq#Index<T>(Seq T, int): T;
      |function Seq#Append<T>(Seq T, Seq T): Seq T;
      |function Seq#Update<T>(Seq T, int, T): Seq T;
      |function Seq#Contains<T>(Seq T, T): bool;
      |function Seq#Take<T>(s: Seq T, howMany: int): Seq T;
      |function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;
      |function Seq#Equal<T>(Seq T, Seq T): bool;
      |function Seq#Sameuntil<T>(Seq T, Seq T, int): bool;
      |
      |axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));
      |
      |axiom (forall<T> :: Seq#Length(Seq#Empty(): Seq T) == 0);
      |axiom (forall<T> s: Seq T :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());
      |
      |
      |axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);
      |
      |// index over build
      |axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Index(Seq#Build(s,v), i) }
      |  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == v) &&
      |  (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == Seq#Index(s, i)));
      |
      |axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
      |  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));
      |
      |axiom (forall<T> t: T :: { Seq#Singleton(t) } Seq#Index(Seq#Singleton(t), 0) == t);
      |
      |axiom (forall<T> x, y: T ::
      |  { Seq#Contains(Seq#Singleton(x),y) }
      |    Seq#Contains(Seq#Singleton(x),y) <==> x==y);
      |
      |axiom (forall<T> s0: Seq T :: { Seq#Append(Seq#Empty(), s0) }
      |  Seq#Append(Seq#Empty(), s0) == s0);
      |
      |axiom (forall<T> s0: Seq T :: { Seq#Append(s0, Seq#Empty()) }
      |  Seq#Append(s0, Seq#Empty()) == s0);
      |
      |axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) } { Seq#Index(s0, n), Seq#Append(s0,s1) }
      |  s0 != Seq#Empty() && s1 != Seq#Empty() ==>
      |  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
      |  (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));
      |
      |axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) }
      |  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
      |
      |axiom (forall<T> s: Seq T, i: int, v: T, n: int :: { Seq#Index(Seq#Update(s,i,v),n) }
      |  0 <= n && n < Seq#Length(s) ==>
      |    (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
      |    (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));
      |
      |axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
      |  Seq#Contains(s,x) <==>
      |    (exists i: int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x));
      |
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
      |axiom (forall<T> s: Seq T, n: int ::
      |  { Seq#Take(s, n) }
      |    n <= 0 ==> Seq#Take(s, n) == Seq#Empty());
      |
      |axiom (forall<T> s: Seq T, n: int, x: T ::
      |  { Seq#Contains(Seq#Take(s, n), x) }
      |  Seq#Contains(Seq#Take(s, n), x) <==>
      |    (exists i: int :: { Seq#Index(s, i) }
      |      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));
      |
      |axiom (forall<T> s: Seq T, n: int ::
      |  { Seq#Drop(s, n) }
      |    n <= 0 ==> Seq#Drop(s, n) == s);
      |
      |axiom (forall<T> s: Seq T, n: int, x: T ::
      |  { Seq#Contains(Seq#Drop(s, n), x) }
      |  Seq#Contains(Seq#Drop(s, n), x) <==>
      |    (exists i: int :: { Seq#Index(s, i) }
      |      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));
      |
      |axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
      |  Seq#Equal(s0,s1) <==>
      |    Seq#Length(s0) == Seq#Length(s1) &&
      |    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
      |        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
      |axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
      |  Seq#Equal(a,b) ==> a == b);
      |
      |axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Sameuntil(s0,s1,n) }
      |  Seq#Sameuntil(s0,s1,n) <==>
      |    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
      |        0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
      |
      |axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) }
      |  0 <= n ==>
      |    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
      |    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));
      |
      |axiom (forall<T> s: Seq T, n: int, j: int ::
      |      { Seq#Index(Seq#Take(s,n), j) }
      |      { Seq#Index(s,j), Seq#Take(s,n) }
      |  0 <= j && j < n && j < Seq#Length(s) ==>
      |    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));
      |
      |axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }
      |  0 <= n ==>
      |    (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
      |    (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));
      |
      |axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) }
      |  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
      |    Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));
      |
      |axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(s, j), Seq#Drop(s,n) }
      |  0 <= n && n <= j && j < Seq#Length(s) ==>
      |    Seq#Index(Seq#Drop(s,n), j - n) == Seq#Index(s, j));
      |
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
      |
      |axiom (forall<T> s: Seq T, v: T, n: int ::
      |        { Seq#Drop(Seq#Build(s, v), n) }
      |        0 <= n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v) );
      |
      |function Seq#Range(min: int, max: int) returns (Seq int);
      |axiom (forall min: int, max: int ::
      |    { Seq#Length(Seq#Range(min, max)) }
      |    (min < max ==> Seq#Length(Seq#Range(min, max)) == max-min) && (max <= min ==> Seq#Length(Seq#Range(min, max)) == 0));
      |axiom (forall min: int, max: int, j: int ::
      |    { Seq#Index(Seq#Range(min, max), j) }
      |    0<=j && j<max-min ==> Seq#Index(Seq#Range(min, max), j) == min + j);
      |
      |axiom (forall min: int, max: int, v: int :: {Seq#Contains(Seq#Range(min, max),v)}
      |  (Seq#Contains(Seq#Range(min, max),v) <==> min <= v && v < max));
      |""".stripMargin
}
