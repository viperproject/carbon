// 
// Translation of Viper program.
// 
// Date:         2018-07-19 12:12:46
// Tool:         carbon 1.0
// Arguments: :  --print sequences.bpl ..\silver\src\test\resources\all\sequences\sequences.sil
// Dependencies:
//   Boogie , located at C:\Program Files\Viper\boogie\Binaries\Boogie.exe.
//   Z3 4.6.1 - 32 bit, located at C:\Program Files\Viper\z3\bin\z3.exe.
// 

// ==================================================
// Preamble of State module.
// ==================================================

function state(Heap: HeapType, Mask: MaskType): bool;

// ==================================================
// Preamble of Heap module.
// ==================================================

type Ref;
var Heap: HeapType;
const null: Ref;
type Field A B;
type NormalField;
type HeapType = <A, B> [Ref, Field A B]B;
const unique $allocated: Field NormalField bool;
axiom (forall o: Ref, f: (Field NormalField Ref), Heap: HeapType ::
  { Heap[o, f] }
  Heap[o, f] == null || Heap[Heap[o, f], $allocated]
);
function IdenticalOnKnownLocations(Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType): bool;
function IsPredicateField<A, B>(f_1: (Field A B)): bool;
function IsWandField<A, B>(f_1: (Field A B)): bool;
function getPredicateId<A, B>(f_1: (Field A B)): int;
// Frame all locations with direct permissions
axiom (forall <A, B> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref, f_2: (Field A B) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[o, f_2] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, o, f_2) ==> Heap[o, f_2] == ExhaleHeap[o, f_2]
);
// Frame all predicate mask locations of predicates with direct permission
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), IsPredicateField(pm_f), ExhaleHeap[null, PredicateMaskField(pm_f)] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsPredicateField(pm_f) ==> Heap[null, PredicateMaskField(pm_f)] == ExhaleHeap[null, PredicateMaskField(pm_f)]
);
// Frame all locations with known folded permissions
axiom (forall <C> Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, pm_f: (Field C FrameType) ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), Heap[null, PredicateMaskField(pm_f)], IsPredicateField(pm_f) } { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[null, PredicateMaskField(pm_f)], IsPredicateField(pm_f) }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> HasDirectPerm(Mask, null, pm_f) && IsPredicateField(pm_f) ==> (forall <A, B> o2: Ref, f_2: (Field A B) ::
    { ExhaleHeap[o2, f_2] }
    Heap[null, PredicateMaskField(pm_f)][o2, f_2] ==> Heap[o2, f_2] == ExhaleHeap[o2, f_2]
  )
);
// All previously-allocated references are still allocated
axiom (forall Heap: HeapType, ExhaleHeap: HeapType, Mask: MaskType, o: Ref ::
  { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), Heap[o, $allocated] } { IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask), ExhaleHeap[o, $allocated] }
  IdenticalOnKnownLocations(Heap, ExhaleHeap, Mask) ==> Heap[o, $allocated] ==> ExhaleHeap[o, $allocated]
);

// ==================================================
// Preamble of Permission module.
// ==================================================

type Perm = real;
type MaskType = <A, B> [Ref, Field A B]Perm;
var Mask: MaskType;
const ZeroMask: MaskType;
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroMask[o_1, f_3] }
  ZeroMask[o_1, f_3] == NoPerm
);
type PMaskType = <A, B> [Ref, Field A B]bool;
const ZeroPMask: PMaskType;
axiom (forall <A, B> o_1: Ref, f_3: (Field A B) ::
  { ZeroPMask[o_1, f_3] }
  !ZeroPMask[o_1, f_3]
);
function PredicateMaskField<A>(f_4: (Field A FrameType)): Field A PMaskType;
const NoPerm: Perm;
axiom NoPerm == 0.000000000;
const FullPerm: Perm;
axiom FullPerm == 1.000000000;
function Perm(a: real, b: real): Perm;
function GoodMask(Mask: MaskType): bool;
axiom (forall Heap: HeapType, Mask: MaskType ::
  { state(Heap, Mask) }
  state(Heap, Mask) ==> GoodMask(Mask)
);
axiom (forall <A, B> Mask: MaskType, o_1: Ref, f_3: (Field A B) ::
  { GoodMask(Mask), Mask[o_1, f_3] }
  GoodMask(Mask) ==> Mask[o_1, f_3] >= NoPerm && ((GoodMask(Mask) && !IsPredicateField(f_3)) && !IsWandField(f_3) ==> Mask[o_1, f_3] <= FullPerm)
);
function HasDirectPerm<A, B>(Mask: MaskType, o_1: Ref, f_3: (Field A B)): bool;
axiom (forall <A, B> Mask: MaskType, o_1: Ref, f_3: (Field A B) ::
  { HasDirectPerm(Mask, o_1, f_3) }
  HasDirectPerm(Mask, o_1, f_3) <==> Mask[o_1, f_3] > NoPerm
);
function sumMask(ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType): bool;
axiom (forall <A, B> ResultMask: MaskType, SummandMask1: MaskType, SummandMask2: MaskType, o_1: Ref, f_3: (Field A B) ::
  { sumMask(ResultMask, SummandMask1, SummandMask2), ResultMask[o_1, f_3] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask1[o_1, f_3] } { sumMask(ResultMask, SummandMask1, SummandMask2), SummandMask2[o_1, f_3] }
  sumMask(ResultMask, SummandMask1, SummandMask2) ==> ResultMask[o_1, f_3] == SummandMask1[o_1, f_3] + SummandMask2[o_1, f_3]
);

// ==================================================
// Preamble of Function and predicate module.
// ==================================================

// Function heights (higher height means its body is available earlier):
// - height 0: trivial
const AssumeFunctionsAbove: int;
// Declarations for function framing
type FrameType;
const EmptyFrame: FrameType;
function FrameFragment<T>(t: T): FrameType;
function ConditionalFrame(p: Perm, f_5: FrameType): FrameType;
function dummyFunction<T>(t: T): bool;
function CombineFrames(a_1: FrameType, b_1: FrameType): FrameType;
// ==================================================
// Definition of conditional frame fragments
// ==================================================

axiom (forall p: Perm, f_5: FrameType ::
  { ConditionalFrame(p, f_5) }
  ConditionalFrame(p, f_5) == (if p > 0.000000000 then f_5 else EmptyFrame)
);
// Function for recording enclosure of one predicate instance in another
function InsidePredicate<A, B>(p: (Field A FrameType), v: FrameType, q: (Field B FrameType), w: FrameType): bool;
// Transitivity of InsidePredicate
axiom (forall <A, B, C> p: (Field A FrameType), v: FrameType, q: (Field B FrameType), w: FrameType, r: (Field C FrameType), u: FrameType ::
  { InsidePredicate(p, v, q, w), InsidePredicate(q, w, r, u) }
  InsidePredicate(p, v, q, w) && InsidePredicate(q, w, r, u) ==> InsidePredicate(p, v, r, u)
);
// Knowledge that two identical instances of the same predicate cannot be inside each other
axiom (forall <A> p: (Field A FrameType), v: FrameType, w: FrameType ::
  { InsidePredicate(p, v, p, w) }
  !InsidePredicate(p, v, p, w)
);

// ==================================================
// Preamble of Sequence module.
// ==================================================

type Seq T;

function Seq#Length<T>(Seq T): int;
axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

function Seq#Empty<T>(): Seq T;
axiom (forall<T> :: Seq#Length(Seq#Empty(): Seq T) == 0);
axiom (forall<T> s: Seq T :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());

function Seq#Singleton<T>(T): Seq T;
axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);
 

function Seq#Build<T>(s: Seq T, val: T): Seq T;
axiom (forall<T> s: Seq T, v: T :: { Seq#Length(Seq#Build(s,v)) }
  Seq#Length(Seq#Build(s,v)) == 1 + Seq#Length(s));
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Index(Seq#Build(s,v), i) }
  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == v) &&
  (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == Seq#Index(s, i)));

function Seq#Append<T>(Seq T, Seq T): Seq T;
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
s0 != Seq#Empty() && s1 != Seq#Empty() ==>
  Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

axiom (forall<T> s: Seq T :: { Seq#Append(Seq#Empty(),s) } Seq#Append(Seq#Empty(),s) == s);
axiom (forall<T> s: Seq T :: { Seq#Append(s,Seq#Empty()) } Seq#Append(s,Seq#Empty()) == s);

function Seq#Index<T>(Seq T, int): T;
axiom (forall<T> t: T :: { Seq#Singleton(t) } Seq#Index(Seq#Singleton(t), 0) == t); // AS: changed trigger

// END BASICS
// START INDEX-APPEND-UPDATE

// extra addition function used to force equalities into the e-graph
function Seq#Add(int, int) : int;
axiom (forall i: int, j: int :: {Seq#Add(i,j)} Seq#Add(i,j) == i + j);
function Seq#Sub(int, int) : int;
axiom (forall i: int, j: int :: {Seq#Sub(i,j)} Seq#Sub(i,j) == i - j);

// AS: split axiom, added constraints
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) } { Seq#Index(s0, n), Seq#Append(s0,s1) } // AS: added alternative trigger
  (s0 != Seq#Empty() && s1 != Seq#Empty() && 0 <= n && n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)));
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) } // term below breaks loops
  s0 != Seq#Empty() && s1 != Seq#Empty() && Seq#Length(s0) <= n && n < Seq#Length(s0) + Seq#Length(s1) ==> Seq#Add(Seq#Sub(n,Seq#Length(s0)),Seq#Length(s0)) == n && Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, Seq#Sub(n,Seq#Length(s0))));
// AS: added "reverse triggering" versions of the axioms
axiom (forall<T> s0: Seq T, s1: Seq T, m: int :: { Seq#Index(s1, m), Seq#Append(s0,s1)}  // m == n-|s0|, n == m + |s0|
  s0 != Seq#Empty() && s1 != Seq#Empty() && 0 <= m && m < Seq#Length(s1) ==> Seq#Sub(Seq#Add(m,Seq#Length(s0)),Seq#Length(s0)) == m && Seq#Index(Seq#Append(s0,s1), Seq#Add(m,Seq#Length(s0))) == Seq#Index(s1, m));


function Seq#Update<T>(Seq T, int, T): Seq T;
axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) } {Seq#Length(s),Seq#Update(s,i,v)} // AS: added trigger
  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
axiom (forall<T> s: Seq T, i: int, v: T, n: int :: { Seq#Index(Seq#Update(s,i,v),n) } { Seq#Index(s,n), Seq#Update(s,i,v) }
  0 <= n && n < Seq#Length(s) ==>
    (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
    (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));

// END INDEX-APPEND-UPDATE
// START TAKE/DROP

function Seq#Take<T>(s: Seq T, howMany: int): Seq T;
// AS: added triggers
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) } { Seq#Take(s,n), Seq#Length(s)}
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));

// ** AS: 2nd of 3 axioms which get instantiated very often in certain problems involving take/drop/append
// AS: added triggers
axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Take(s,n), j) } {Seq#Index(s,j), Seq#Take(s,n)} // {:weight 25} // AS: dropped weight
  0 <= j && j < n && j < Seq#Length(s) ==>
    Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));

function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;
axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }{Seq#Length(s), Seq#Drop(s,n)}
  0 <= n ==>
    (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
    (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));

// ** AS: 3rd of 3 axioms which get instantiated very often in certain problems involving take/drop/append
// split axiom
axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) } // {:weight 25} // AS: dropped weight
  0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
   Seq#Sub(Seq#Add(j,n),n) == j && Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, Seq#Add(j,n)));

axiom (forall<T> s: Seq T, n: int, i: int :: { Seq#Drop(s,n), Seq#Index(s,i) }
  0 <= n && n <= i && i < Seq#Length(s) ==>
  Seq#Add(Seq#Sub(i,n),n) == i && Seq#Index(Seq#Drop(s,n), Seq#Sub(i,n)) == Seq#Index(s, i)); // i = j + n, j = i - n

// ** AS: We dropped the weak trigger on this axiom. One option is to strengthen the triggers:
//axiom (forall<T> s, t: Seq T ::
 //// { Seq#Append(s, t) }
//  {Seq#Take(Seq#Append(s, t), Seq#Length(s))}{Seq#Drop(Seq#Append(s, t), Seq#Length(s))}
//  Seq#Take(Seq#Append(s, t), Seq#Length(s)) == s &&
//  Seq#Drop(Seq#Append(s, t), Seq#Length(s)) == t);

// ** AS: another option is to split the axiom (for some reason, this seems in some cases to perform slightly less well (but this could be random):
//axiom (forall<T> s, t: Seq T ::
// { Seq#Take(Seq#Append(s, t), Seq#Length(s)) }
//  Seq#Take(Seq#Append(s, t), Seq#Length(s)) == s);

//axiom (forall<T> s, t: Seq T ::
// { Seq#Drop(Seq#Append(s, t), Seq#Length(s)) }
//  Seq#Drop(Seq#Append(s, t), Seq#Length(s)) == t);

// Commutability of Take and Drop with Update.
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Take(Seq#Update(s, i, v), n) }
        0 <= i && i < n && n <= Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Take(Seq#Update(s, i, v), n) }
        n <= i && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Drop(Seq#Update(s, i, v), n) }
        0 <= n && n <= i && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
        { Seq#Drop(Seq#Update(s, i, v), n) }
        0 <= i && i < n && n < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
// drop commutes with build.
axiom (forall<T> s: Seq T, v: T, n: int ::
        { Seq#Drop(Seq#Build(s, v), n) }
        0 <= n && n <= Seq#Length(s) ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v) );

// Additional axioms about common things
axiom (forall<T> s: Seq T, n: int :: { Seq#Drop(s, n) } // ** NEW
        n <= 0 ==> Seq#Drop(s, n) == s);
axiom (forall<T> s: Seq T, n: int :: { Seq#Take(s, n) } // ** NEW
        n <= 0 ==> Seq#Take(s, n) == Seq#Empty());
axiom (forall<T> s: Seq T, m, n: int :: { Seq#Drop(Seq#Drop(s, m), n) } // ** NEW - AS: could have bad triggering behaviour?
        0 <= m && 0 <= n && m+n <= Seq#Length(s) ==>
        Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m+n));

// END TAKE/DROP

// START CONTAINS

function Seq#Skolem<T>(Seq T, T) : int; // skolem function for Seq#Contains
function Seq#SkolemContainsDrop<T>(Seq T, int, T) : int; // skolem function for Seq#Contains over drop
function Seq#SkolemContainsTake<T>(Seq T, int, T) : int; // skolem function for Seq#Contains over take

function Seq#Contains<T>(Seq T, T): bool;
axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
  Seq#Contains(s,x) ==> s != Seq#Empty() && Seq#Length(s) > 0 && 0 <= Seq#Skolem(s,x) &&
    Seq#Skolem(s,x) < Seq#Length(s) && Seq#Index(s,Seq#Skolem(s,x)) == x);

// AS: note: this is an unusual axiom, but is basically the original
// Consider writing a version without the (precise) first trigger? Also see later versions
axiom (forall<T> s: Seq T, x: T, i:int :: { Seq#Contains(s,x), Seq#Index(s,i) }
  0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x ==> Seq#Contains(s,x));

// ** AS: made one change here - changed type of x from ref to T
axiom (forall<T> x: T ::
  { Seq#Contains(Seq#Empty(), x) }
  !Seq#Contains(Seq#Empty(), x));

// AS: Consider dropping this axiom?
axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
  { Seq#Contains(Seq#Append(s0, s1), x) } { Seq#Contains(s0,x), Seq#Append(s0,s1)} { Seq#Contains(s1,x), Seq#Append(s0,s1)} // AS: added triggers
  Seq#Contains(Seq#Append(s0, s1), x) <==>
    Seq#Contains(s0, x) || Seq#Contains(s1, x));

axiom (forall<T> s: Seq T, v: T, x: T ::
  { Seq#Contains(Seq#Build(s, v), x) } {Seq#Contains(s,x), Seq#Build(s, v)}
    Seq#Contains(Seq#Build(s, v), x) <==> (v == x || Seq#Contains(s, x)));

// AS: split axioms
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Take(s, n), x) }
  Seq#Contains(Seq#Take(s, n), x) ==>
    (Seq#Take(s, n) != Seq#Empty() && Seq#Length(Seq#Take(s, n)) > 0 &&
     0 <= Seq#SkolemContainsTake(s, n, x) && Seq#SkolemContainsTake(s, n, x) < n &&
      Seq#SkolemContainsTake(s, n, x) < Seq#Length(s) &&
      Seq#Index(s, Seq#SkolemContainsTake(s, n, x)) == x));

axiom (forall<T> s: Seq T, n: int, x: T, i:int ::
  { Seq#Contains(Seq#Take(s, n), x), Seq#Index(s, i) }
    0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x ==>
     Seq#Contains(Seq#Take(s, n), x));

// AS: split axioms
axiom (forall<T> s: Seq T, n: int, x: T ::
  { Seq#Contains(Seq#Drop(s, n), x) }
  Seq#Contains(Seq#Drop(s, n), x) ==>
    ( 0 <= Seq#SkolemContainsDrop(s, n, x) && n <= Seq#SkolemContainsDrop(s, n, x) &&
      Seq#SkolemContainsDrop(s, n, x) < Seq#Length(s) &&
      Seq#Index(s, Seq#SkolemContainsDrop(s, n, x)) == x));

axiom (forall<T> s: Seq T, n: int, x: T, i:int ::
  { Seq#Contains(Seq#Drop(s, n), x), Seq#Index(s, i) }
  0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x ==>
  Seq#Contains(Seq#Drop(s, n), x));

// END CONTAINS

// START EQUALS

function Seq#Equal<T>(Seq T, Seq T): bool;

// AS: split axiom
axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
  Seq#Equal(s0,s1) ==>
    Seq#Length(s0) == Seq#Length(s1) &&
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

function Seq#SkolemDiff<T>(Seq T, Seq T) : int; // skolem function for Seq#Equals

axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
  Seq#Length(s0) != Seq#Length(s1) ||
        (0 <= Seq#SkolemDiff(s0,s1) && Seq#SkolemDiff(s0,s1) < Seq#Length(s0) &&
         Seq#Index(s0,Seq#SkolemDiff(s0,s1)) != Seq#Index(s1,Seq#SkolemDiff(s0,s1))) || s0==s1);

axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
  Seq#Equal(a,b) ==> a == b);

function Seq#SameUntil<T>(Seq T, Seq T, int): bool;
axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#SameUntil(s0,s1,n) }
  Seq#SameUntil(s0,s1,n) <==>
    (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

// END EQUALS


// START EXTRAS

// extra stuff not in current Dafny Prelude

axiom (forall<T> x, y: T ::
  { Seq#Contains(Seq#Singleton(x),y) }
    Seq#Contains(Seq#Singleton(x),y) ==> x==y);

axiom (forall<T> x: T ::
  { Seq#Singleton(x) }
    Seq#Contains(Seq#Singleton(x),x));


function Seq#Range(min: int, max: int) returns (Seq int);
axiom (forall min: int, max: int :: { Seq#Length(Seq#Range(min, max)) } (min < max ==> Seq#Length(Seq#Range(min, max)) == max-min) && (max <= min ==> Seq#Length(Seq#Range(min, max)) == 0));
axiom (forall min: int, max: int, j: int :: { Seq#Index(Seq#Range(min, max), j) } 0<=j && j<max-min ==> Seq#Index(Seq#Range(min, max), j) == min + j);

axiom (forall min: int, max: int, v: int :: {Seq#Contains(Seq#Range(min, max),v)}
  (Seq#Contains(Seq#Range(min, max),v) <==> min <= v && v < max));

// END EXTRAS


// ==================================================
// Translation of function trivial
// ==================================================

// Uninterpreted function definitions
function trivial(Heap: HeapType, i: int): bool;
function trivial'(Heap: HeapType, i: int): bool;
axiom (forall Heap: HeapType, i: int ::
  { trivial(Heap, i) }
  trivial(Heap, i) == trivial'(Heap, i) && dummyFunction(trivial#triggerStateless(i))
);
axiom (forall Heap: HeapType, i: int ::
  { trivial'(Heap, i) }
  dummyFunction(trivial#triggerStateless(i))
);

// Definitional axiom
axiom (forall Heap: HeapType, Mask: MaskType, i: int ::
  { state(Heap, Mask), trivial(Heap, i) }
  state(Heap, Mask) && AssumeFunctionsAbove < 0 ==> trivial(Heap, i)
);

// Framing axioms
function trivial#frame(frame: FrameType, i: int): bool;
axiom (forall Heap: HeapType, Mask: MaskType, i: int ::
  { state(Heap, Mask), trivial'(Heap, i) }
  state(Heap, Mask) ==> trivial'(Heap, i) == trivial#frame(EmptyFrame, i)
);

// Trigger function (controlling recursive postconditions)
function trivial#trigger(frame: FrameType, i: int): bool;

// State-independent trigger function
function trivial#triggerStateless(i: int): bool;

// Check contract well-formedness and postcondition
procedure trivial#definedness(i: int) returns (Result: bool)
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == 0;
  
  // -- Initializing the old state
    assume Heap == old(Heap);
    assume Mask == old(Mask);
  
  // -- Translate function body
    Result := true;
}

// ==================================================
// Translation of method t1
// ==================================================

procedure t1(x: int, xs: (Seq int)) returns ()
  modifies Heap, Mask;
{
  var n: (Seq int);
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: n := Seq[Int]() -- sequences.sil@3.5
    n := (Seq#Empty(): Seq int);
    assume state(Heap, Mask);
  
  // -- Translating statement: assert |n| == 0 -- sequences.sil@4.5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion |n| == 0 might not hold. (sequences.sil@4.5) [111]"}
      Seq#Length(n) == 0;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert n != Seq(x) -- sequences.sil@5.5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion n != Seq(x) might not hold. (sequences.sil@5.5) [112]"}
      !Seq#Equal(n, Seq#Singleton(x));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert |Seq(1)| == 1 -- sequences.sil@6.5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion |Seq(1)| == 1 might not hold. (sequences.sil@6.5) [113]"}
      Seq#Length(Seq#Singleton(1)) == 1;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert |Seq(0)| == 0 -- sequences.sil@8.5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion |Seq(0)| == 0 might not hold. (sequences.sil@8.5) [114]"}
      Seq#Length(Seq#Singleton(0)) == 0;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method t2
// ==================================================

procedure t2() returns ()
  modifies Heap, Mask;
{
  var a_2: (Seq int);
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: assert (1 in Seq(1, 2, 3)) -- sequences.sil@12.5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion (1 in Seq(1, 2, 3)) might not hold. (sequences.sil@12.5) [115]"}
      Seq#Contains(Seq#Append(Seq#Append(Seq#Singleton(1), Seq#Singleton(2)), Seq#Singleton(3)), 1);
    assume state(Heap, Mask);
  
  // -- Translating statement: assert |[-1..10)| == 11 -- sequences.sil@13.5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion |[-1..10)| == 11 might not hold. (sequences.sil@13.5) [116]"}
      Seq#Length(Seq#Range(-1, 10)) == 11;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert Seq(1) ++ Seq(2) == Seq(1, 2) -- sequences.sil@14.5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion Seq(1) ++ Seq(2) == Seq(1, 2) might not hold. (sequences.sil@14.5) [117]"}
      Seq#Equal(Seq#Append(Seq#Singleton(1), Seq#Singleton(2)), Seq#Append(Seq#Singleton(1), Seq#Singleton(2)));
    assume state(Heap, Mask);
  
  // -- Translating statement: a := Seq(0, 1, -11, 22) -- sequences.sil@16.5
    a_2 := Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(0), Seq#Singleton(1)), Seq#Singleton(-11)), Seq#Singleton(22));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert a[2] == -11 -- sequences.sil@17.5
    
    // -- Check definedness of a[2] == -11
      assert {:msg "  Assert might fail. Index a[2] into a might exceed sequence length. (sequences.sil@17.5) [118]"}
        2 < Seq#Length(a_2);
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion a[2] == -11 might not hold. (sequences.sil@17.5) [119]"}
      Seq#Index(a_2, 2) == -11;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert a[..1] == Seq(0) -- sequences.sil@19.5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion a[..1] == Seq(0) might not hold. (sequences.sil@19.5) [120]"}
      Seq#Equal(Seq#Take(a_2, 1), Seq#Singleton(0));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert a[1..] == Seq(1, -11, 22) -- sequences.sil@20.5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion a[1..] == Seq(1, -11, 22) might not hold. (sequences.sil@20.5) [121]"}
      Seq#Equal(Seq#Drop(a_2, 1), Seq#Append(Seq#Append(Seq#Singleton(1), Seq#Singleton(-11)), Seq#Singleton(22)));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert a[1..2] == Seq(1) -- sequences.sil@21.5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion a[1..2] == Seq(1) might not hold. (sequences.sil@21.5) [122]"}
      Seq#Equal(Seq#Drop(Seq#Take(a_2, 2), 1), Seq#Singleton(1));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert a[1 := 22] == a[1 := -1][1 := 22] -- sequences.sil@23.5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion a[1 := 22] == a[1 := -1][1 := 22] might not hold. (sequences.sil@23.5) [123]"}
      Seq#Equal(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(22), Seq#Drop(a_2, 2))), Seq#Append(Seq#Take(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(-1), Seq#Drop(a_2, 2))), 1), Seq#Append(Seq#Singleton(22), Seq#Drop(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(-1), Seq#Drop(a_2, 2))), 2))));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert a[1 := 22] == Seq(0, 22, -11, 22) -- sequences.sil@24.5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion a[1 := 22] == Seq(0, 22, -11, 22) might not hold. (sequences.sil@24.5) [124]"}
      Seq#Equal(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(22), Seq#Drop(a_2, 2))), Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(0), Seq#Singleton(22)), Seq#Singleton(-11)), Seq#Singleton(22)));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert |a[1 := 22]| == 4 -- sequences.sil@25.5
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion |a[1 := 22]| == 4 might not hold. (sequences.sil@25.5) [125]"}
      Seq#Length(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(22), Seq#Drop(a_2, 2)))) == 4;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert a[1 := 22][1] == 22 -- sequences.sil@26.5
    
    // -- Check definedness of a[1 := 22][1] == 22
      assert {:msg "  Assert might fail. Index a[1 := 22][1] into a[1 := 22] might exceed sequence length. (sequences.sil@26.5) [126]"}
        1 < Seq#Length(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(22), Seq#Drop(a_2, 2))));
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion a[1 := 22][1] == 22 might not hold. (sequences.sil@26.5) [127]"}
      Seq#Index(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(22), Seq#Drop(a_2, 2))), 1) == 22;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert a[1 := 22][2] == -11 -- sequences.sil@27.5
    
    // -- Check definedness of a[1 := 22][2] == -11
      assert {:msg "  Assert might fail. Index a[1 := 22][2] into a[1 := 22] might exceed sequence length. (sequences.sil@27.5) [128]"}
        2 < Seq#Length(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(22), Seq#Drop(a_2, 2))));
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion a[1 := 22][2] == -11 might not hold. (sequences.sil@27.5) [129]"}
      Seq#Index(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(22), Seq#Drop(a_2, 2))), 2) == -11;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert a[1 := 22][0] == 22 -- sequences.sil@29.5
    
    // -- Check definedness of a[1 := 22][0] == 22
      assert {:msg "  Assert might fail. Index a[1 := 22][0] into a[1 := 22] might exceed sequence length. (sequences.sil@29.5) [130]"}
        0 < Seq#Length(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(22), Seq#Drop(a_2, 2))));
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion a[1 := 22][0] == 22 might not hold. (sequences.sil@29.5) [131]"}
      Seq#Index(Seq#Append(Seq#Take(a_2, 1), Seq#Append(Seq#Singleton(22), Seq#Drop(a_2, 2))), 0) == 22;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method test3
// ==================================================

procedure test3() returns ()
  modifies Heap, Mask;
{
  var xs: (Seq int);
  var bs: (Seq bool);
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: xs := Seq(0, 1, 2, 3, 4, 5, 6, 7) -- sequences.sil@33.3
    xs := Seq#Append(Seq#Append(Seq#Append(Seq#Append(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(0), Seq#Singleton(1)), Seq#Singleton(2)), Seq#Singleton(3)), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)), Seq#Singleton(7));
    assume state(Heap, Mask);
  
  // -- Translating statement: bs := Seq(true, true, false, true) ++ Seq(false, true) -- sequences.sil@34.3
    bs := Seq#Append(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(true), Seq#Singleton(true)), Seq#Singleton(false)), Seq#Singleton(true)), Seq#Append(Seq#Singleton(false), Seq#Singleton(true)));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert |xs[1..][..6]| == |bs| -- sequences.sil@36.3
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion |xs[1..][..6]| == |bs| might not hold. (sequences.sil@36.3) [132]"}
      Seq#Length(Seq#Take(Seq#Drop(xs, 1), 6)) == Seq#Length(bs);
    assume state(Heap, Mask);
  
  // -- Translating statement: assert |xs[1..]| == |xs| -- sequences.sil@38.3
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion |xs[1..]| == |xs| might not hold. (sequences.sil@38.3) [133]"}
      Seq#Length(Seq#Drop(xs, 1)) == Seq#Length(xs);
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method test4
// ==================================================

procedure test4(s: (Seq int), i: int, j: int) returns ()
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Checked inhaling of precondition
    assume 0 <= i;
    assume state(Heap, Mask);
    assume i <= j;
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: assert s == s[..i] ++ s[i..] -- sequences.sil@45.3
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion s == s[..i] ++ s[i..] might not hold. (sequences.sil@45.3) [134]"}
      Seq#Equal(s, Seq#Append(Seq#Take(s, i), Seq#Drop(s, i)));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert s == s[..i] ++ s[i..j] ++ s[j..] -- sequences.sil@46.3
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion s == s[..i] ++ s[i..j] ++ s[j..] might not hold. (sequences.sil@46.3) [135]"}
      Seq#Equal(s, Seq#Append(Seq#Append(Seq#Take(s, i), Seq#Drop(Seq#Take(s, j), i)), Seq#Drop(s, j)));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert s[..i] ++ s[i..j] ++ s[j..] == s[..i] ++ (s[i..j] ++ s[j..]) -- sequences.sil@47.3
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion s[..i] ++ s[i..j] ++ s[j..] == s[..i] ++ (s[i..j] ++ s[j..]) might not hold. (sequences.sil@47.3) [136]"}
      Seq#Equal(Seq#Append(Seq#Append(Seq#Take(s, i), Seq#Drop(Seq#Take(s, j), i)), Seq#Drop(s, j)), Seq#Append(Seq#Take(s, i), Seq#Append(Seq#Drop(Seq#Take(s, j), i), Seq#Drop(s, j))));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert |s[j..]| == |s| - j -- sequences.sil@49.3
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion |s[j..]| == |s| - j might not hold. (sequences.sil@49.3) [137]"}
      Seq#Length(Seq#Drop(s, j)) == Seq#Length(s) - j;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method test5
// ==================================================

procedure test5(s: (Seq int), i: int, j: int) returns ()
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: assert s == s[..i] ++ s[i..] -- sequences.sil@57.3
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion s == s[..i] ++ s[i..] might not hold. (sequences.sil@57.3) [138]"}
      Seq#Equal(s, Seq#Append(Seq#Take(s, i), Seq#Drop(s, i)));
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method test6
// ==================================================

procedure test6() returns ()
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: assert Seq(3, 4, 5, 6)[0] == 3 -- sequences.sil@61.3
    
    // -- Check definedness of Seq(3, 4, 5, 6)[0] == 3
      assert {:msg "  Assert might fail. Index Seq(3, 4, 5, 6)[0] into Seq(3, 4, 5, 6) might exceed sequence length. (sequences.sil@61.3) [139]"}
        0 < Seq#Length(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)));
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion Seq(3, 4, 5, 6)[0] == 3 might not hold. (sequences.sil@61.3) [140]"}
      Seq#Index(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)), 0) == 3;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert Seq(3, 4, 5, 6)[1] == 4 -- sequences.sil@62.3
    
    // -- Check definedness of Seq(3, 4, 5, 6)[1] == 4
      assert {:msg "  Assert might fail. Index Seq(3, 4, 5, 6)[1] into Seq(3, 4, 5, 6) might exceed sequence length. (sequences.sil@62.3) [141]"}
        1 < Seq#Length(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)));
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion Seq(3, 4, 5, 6)[1] == 4 might not hold. (sequences.sil@62.3) [142]"}
      Seq#Index(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)), 1) == 4;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert Seq(3, 4, 5, 6)[2] == 5 -- sequences.sil@63.3
    
    // -- Check definedness of Seq(3, 4, 5, 6)[2] == 5
      assert {:msg "  Assert might fail. Index Seq(3, 4, 5, 6)[2] into Seq(3, 4, 5, 6) might exceed sequence length. (sequences.sil@63.3) [143]"}
        2 < Seq#Length(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)));
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion Seq(3, 4, 5, 6)[2] == 5 might not hold. (sequences.sil@63.3) [144]"}
      Seq#Index(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)), 2) == 5;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert Seq(3, 4, 5, 6)[3] == 6 -- sequences.sil@64.3
    
    // -- Check definedness of Seq(3, 4, 5, 6)[3] == 6
      assert {:msg "  Assert might fail. Index Seq(3, 4, 5, 6)[3] into Seq(3, 4, 5, 6) might exceed sequence length. (sequences.sil@64.3) [145]"}
        3 < Seq#Length(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)));
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion Seq(3, 4, 5, 6)[3] == 6 might not hold. (sequences.sil@64.3) [146]"}
      Seq#Index(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)), 3) == 6;
    assume state(Heap, Mask);
  
  // -- Translating statement: assert Seq(3, 4, 5, 6)[3] == 5 -- sequences.sil@66.3
    
    // -- Check definedness of Seq(3, 4, 5, 6)[3] == 5
      assert {:msg "  Assert might fail. Index Seq(3, 4, 5, 6)[3] into Seq(3, 4, 5, 6) might exceed sequence length. (sequences.sil@66.3) [147]"}
        3 < Seq#Length(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)));
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion Seq(3, 4, 5, 6)[3] == 5 might not hold. (sequences.sil@66.3) [148]"}
      Seq#Index(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)), 3) == 5;
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method test_index_definedness_small
// ==================================================

procedure test_index_definedness_small(i: int) returns ()
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Checked inhaling of precondition
    assume i < 4;
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: assert trivial(Seq(3, 4, 5, 6)[i]) -- sequences.sil@75.3
    
    // -- Check definedness of trivial(Seq(3, 4, 5, 6)[i])
      assert {:msg "  Assert might fail. Index Seq(3, 4, 5, 6)[i] into Seq(3, 4, 5, 6) might be negative. (sequences.sil@75.3) [149]"}
        i >= 0;
      assert {:msg "  Assert might fail. Index Seq(3, 4, 5, 6)[i] into Seq(3, 4, 5, 6) might exceed sequence length. (sequences.sil@75.3) [150]"}
        i < Seq#Length(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)));
      if (*) {
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion trivial(Seq(3, 4, 5, 6)[i]) might not hold. (sequences.sil@75.3) [151]"}
      trivial(Heap, Seq#Index(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)), i));
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method test_index_definedness_large
// ==================================================

procedure test_index_definedness_large(i: int) returns ()
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Checked inhaling of precondition
    assume i >= 0;
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: assert trivial(Seq(3, 4, 5, 6)[i]) -- sequences.sil@82.3
    
    // -- Check definedness of trivial(Seq(3, 4, 5, 6)[i])
      assert {:msg "  Assert might fail. Index Seq(3, 4, 5, 6)[i] into Seq(3, 4, 5, 6) might be negative. (sequences.sil@82.3) [152]"}
        i >= 0;
      assert {:msg "  Assert might fail. Index Seq(3, 4, 5, 6)[i] into Seq(3, 4, 5, 6) might exceed sequence length. (sequences.sil@82.3) [153]"}
        i < Seq#Length(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)));
      if (*) {
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion trivial(Seq(3, 4, 5, 6)[i]) might not hold. (sequences.sil@82.3) [154]"}
      trivial(Heap, Seq#Index(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)), i));
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method test_build_index_definedness_small
// ==================================================

procedure test_build_index_definedness_small(i: int) returns ()
  modifies Heap, Mask;
{
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Checked inhaling of precondition
    assume i < 4;
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: assert trivial(Seq(3, 4, 5, 6)[i := 3][0]) -- sequences.sil@92.3
    
    // -- Check definedness of trivial(Seq(3, 4, 5, 6)[i := 3][0])
      assert {:msg "  Assert might fail. Index Seq(3, 4, 5, 6)[i := 3][0] into Seq(3, 4, 5, 6)[i := 3] might exceed sequence length. (sequences.sil@92.3) [155]"}
        0 < Seq#Length(Seq#Append(Seq#Take(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)), i), Seq#Append(Seq#Singleton(3), Seq#Drop(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)), i + 1))));
      if (*) {
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion trivial(Seq(3, 4, 5, 6)[i := 3][0]) might not hold. (sequences.sil@92.3) [156]"}
      trivial(Heap, Seq#Index(Seq#Append(Seq#Take(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)), i), Seq#Append(Seq#Singleton(3), Seq#Drop(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)), i + 1))), 0));
    assume state(Heap, Mask);
}

// ==================================================
// Translation of method test_build_index_definedness_large
// ==================================================

procedure test_build_index_definedness_large(i: int) returns ()
  modifies Heap, Mask;
{
  var s: (Seq int);
  
  // -- Initializing the state
    Mask := ZeroMask;
    assume state(Heap, Mask);
    assume AssumeFunctionsAbove == -1;
  
  // -- Checked inhaling of precondition
    assume i >= 0;
    assume state(Heap, Mask);
  
  // -- Initializing of old state
    
    // -- Initializing the old state
      assume Heap == old(Heap);
      assume Mask == old(Mask);
  
  // -- Translating statement: s := Seq(3, 4, 5, 6)[i := 3] -- sequences.sil@101.3
    s := Seq#Append(Seq#Take(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)), i), Seq#Append(Seq#Singleton(3), Seq#Drop(Seq#Append(Seq#Append(Seq#Append(Seq#Singleton(3), Seq#Singleton(4)), Seq#Singleton(5)), Seq#Singleton(6)), i + 1)));
    assume state(Heap, Mask);
  
  // -- Translating statement: assert trivial(s[0]) -- sequences.sil@103.3
    
    // -- Check definedness of trivial(s[0])
      assert {:msg "  Assert might fail. Index s[0] into s might exceed sequence length. (sequences.sil@103.3) [157]"}
        0 < Seq#Length(s);
      if (*) {
        // Stop execution
        assume false;
      }
      assume state(Heap, Mask);
    // Phase 1: pure assertions and fixed permissions
    assert {:msg "  Assert might fail. Assertion trivial(s[0]) might not hold. (sequences.sil@103.3) [158]"}
      trivial(Heap, Seq#Index(s, 0));
    assume state(Heap, Mask);
}