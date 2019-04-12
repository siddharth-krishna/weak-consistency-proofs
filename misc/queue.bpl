// ----------------------------------------
// A simple queue implementation based on the Michael-Scott queue.
// Assumes GC, so does not free dequeued nodes.
// Uses the simplified heap encoding from CIVL's Treiber example.
// But uses FP sets for linearity instead of Heaps and dom(heap).
//
// Use options -noinfer -typeEncoding:m -useArrayTheory
// ----------------------------------------


// ---------- Types of methods and invocations

type Method;

type Invoc;

// Boilerplate stuff for linear variables
function {:builtin "MapConst"} MapConstInvocBool(bool) : [Invoc]bool;
function {:inline} {:linear "this"} TidCollector(x: Invoc) : [Invoc]bool
{
  MapConstInvocBool(false)[x := true]
}


// ---------- Types and axiomatization of sequences (of invocations)

// Sequences of invocations
type SeqInvoc;

function Seq_append(s: SeqInvoc, o: Invoc) returns (t: SeqInvoc);

function Seq_elem(n: Invoc, s: SeqInvoc) : bool;

// Relationship between elem and append
axiom (forall n1, n2: Invoc, s: SeqInvoc :: {Seq_elem(n1, Seq_append(s, n2))}
       Seq_elem(n1, s) ==> Seq_elem(n1, Seq_append(s, n2)));

axiom (forall n: Invoc, s: SeqInvoc :: {Seq_elem(n, Seq_append(s, n))}
       Seq_elem(n, Seq_append(s, n)));


// ---------- Types and axiomatization of sets (of invocations)

// Sets of invocations
type SetInvoc;
const Set_empty: SetInvoc;

function Set_elem(n: Invoc, s: SetInvoc) : bool;

function Set_subset(s: SetInvoc, t: SetInvoc) : bool;

// Set_empty is a subset of anything
axiom (forall s: SetInvoc :: Set_subset(Set_empty, s));

// Nothing is an elem of Set_empty
axiom (forall n: Invoc :: !Set_elem(n, Set_empty));

// subset is reflexive
axiom (forall s: SetInvoc :: Set_subset(s, s));

// subset is transitive
axiom (forall s, t, u: SetInvoc :: Set_subset(s, t) && Set_subset(t, u) ==> Set_subset(s, u));

// definition of subset in terms of elem
axiom (forall s, t: SetInvoc :: (forall n: Invoc :: Set_elem(n, s) ==> Set_elem(n, t)) ==> Set_subset(s, t));

function Set_union(s1: SetInvoc, s2: SetInvoc) returns (t: SetInvoc);

// union is idempotent
axiom (forall s: SetInvoc :: s == Set_union(s, s));

// union is associative
axiom (forall s, t: SetInvoc :: Set_union(s, t) == Set_union(t, s));

// union is monotonic w.r.t subset
axiom (forall s, t1, t2: SetInvoc :: Set_subset(t1, t2) ==> Set_subset(Set_union(s, t1), Set_union(s, t2)));

axiom (forall s, t1, t2: SetInvoc :: Set_subset(t1, s) && Set_subset(t2, s) ==> Set_subset(Set_union(t1, t2), s));

// relation between union and elem
axiom (forall n: Invoc, s, s1, t: SetInvoc :: Set_elem(n, s) && s1 == Set_union(s, t) ==> Set_elem(n, s1));

// Calculate the union m[i] \cup ... \cup m[j-1]
function unionRange(m: [int]SetInvoc, i: int, j: int) returns (s: SetInvoc);

function Set_ofSeq(q: SeqInvoc) returns (s: SetInvoc);

function Set_add(s: SetInvoc, n: Invoc) returns (t: SetInvoc);

// Relation between add and elem
axiom (forall s: SetInvoc, n1, n2: Invoc :: Set_elem(n1, Set_add(s, n2))
       ==> n1 == n2 || Set_elem(n1, s));
axiom (forall s: SetInvoc, n1, n2: Invoc :: Set_elem(n1, s) ==> Set_elem(n1, Set_add(s, n2)));

// Relation between union and elem
axiom (forall s, t: SetInvoc, n1: Invoc :: Set_elem(n1, Set_union(s, t))
       ==> Set_elem(n1, s) || Set_elem(n1, t));

// add preserves subset relation
axiom (forall s, t: SetInvoc, n: Invoc :: Set_subset(s, t) ==> Set_subset(Set_add(s, n), Set_add(t, n)));
axiom (forall s, t: SetInvoc, n: Invoc :: Set_subset(s, t) ==> Set_subset(s, Set_add(t, n)));

// Relation between setOfSeq, add, and append
axiom (forall q: SeqInvoc, n: Invoc :: Set_ofSeq(Seq_append(q, n)) == Set_add(Set_ofSeq(q), n));

// Relation between unionRange, add, and append
axiom (forall t: [int]SetInvoc, i, j, k: int, q: SeqInvoc, n: Invoc ::
        unionRange(t, i, j) == Set_ofSeq(q) && i <= k && k < j
        ==> unionRange(t[k := Set_add(t[k], n)], i, j) == Set_ofSeq(Seq_append(q, n)));

// Add n to m[i], ..., m[j-1]
function addRange(m: [int]SetInvoc, n: Invoc, i: int, j: int)
  returns (m1: [int]SetInvoc);

// The effect of addRange
axiom (forall m, m1: [int]SetInvoc, n: Invoc, i: int, j: int, k: int ::
        m1 == addRange(m, n, i, j) && i <= k && k < j
        ==> m1[k] == Set_add(m[k], n));
axiom (forall m, m1: [int]SetInvoc, n: Invoc, i: int, j: int, k: int ::
        m1 == addRange(m, n, i, j) && !(i <= k && k < j)
        ==> m1[k] == m[k]);

// What happens to unionRange and setOfSeq when you do an addRange
axiom (forall t: [int]SetInvoc, i, j, i1, j1: int, q: SeqInvoc, n: Invoc ::
        unionRange(t, i, j) == Set_ofSeq(q) && i <= i1 && i1 < j1 && j1 <= j ==>
          unionRange(addRange(t, n, i1, j1), i, j) == Set_ofSeq(Seq_append(q, n)));


// ---------- Axioms of the queue ADT

const unique Queue.push, Queue.pop, Queue.size: Method;

function invoc_m(n: Invoc) : Method;
function invoc_k(n: Invoc) : Key;

type Queue.State;

function Queue.stateArray(s: Queue.State) : [int]Key;
function Queue.stateHead(s: Queue.State) : int;
function Queue.stateTail(s: Queue.State) : int;

function Queue.ofSeq(s: SeqInvoc) : Queue.State;

axiom (forall s: SeqInvoc, n: Invoc :: {Queue.ofSeq(Seq_append(s, n))}
  invoc_m(n) == Queue.pop // TODO empty?
  ==> Queue.stateHead(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateHead(Queue.ofSeq(s)) + 1
  && Queue.stateTail(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateTail(Queue.ofSeq(s))
  && Queue.stateArray(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateArray(Queue.ofSeq(s)));


// ---------- Representation of execution and linearization

// hb(x, y) : x happens-before y.
// We assume there exists such a function, given by the client program
function hb(x: Invoc, y: Invoc) : bool;
axiom (forall n: Invoc :: !hb(n, n));

// A shared global variable that builds the linearization
var {:layer 1,2} lin: SeqInvoc;

// A map from invocations to the set of prior invocations visible to them
var {:layer 1,2} vis: [Invoc]SetInvoc;

// The set of invocations that have been called
var {:layer 0,1} called: [Invoc]bool;

// The set of invocations that have returned
var {:layer 0,1} returned: [Invoc]bool;


// ---------- Heap representation and linearity


type Ref;
const null: Ref;

function {:builtin "MapConst"} MapConstBool(bool) : [Ref]bool;

const emptySet : [Ref]bool;
axiom (emptySet == MapConstBool(false));

// Linearity stuff:

function {:inline} {:linear "FP"} FPCollector(x: [Ref]bool) : [Ref]bool { x }


// ---------- Reachability, between, and associated theories

function Equal([Ref]bool, [Ref]bool) returns (bool);
function Subset([Ref]bool, [Ref]bool) returns (bool);

function Empty() returns ([Ref]bool);
function Singleton(Ref) returns ([Ref]bool);
function Union([Ref]bool, [Ref]bool) returns ([Ref]bool);

axiom(forall x:Ref :: !Empty()[x]);

axiom(forall x:Ref, y:Ref :: {Singleton(y)[x]} Singleton(y)[x] <==> x == y);
axiom(forall y:Ref :: {Singleton(y)} Singleton(y)[y]);

axiom(forall x:Ref, S:[Ref]bool, T:[Ref]bool :: {Union(S,T)[x]}{Union(S,T),S[x]}{Union(S,T),T[x]} Union(S,T)[x] <==> S[x] || T[x]);

axiom(forall S:[Ref]bool, T:[Ref]bool :: {Equal(S,T)} Equal(S,T) <==> Subset(S,T) && Subset(T,S));
axiom(forall x:Ref, S:[Ref]bool, T:[Ref]bool :: {S[x],Subset(S,T)}{T[x],Subset(S,T)} S[x] && Subset(S,T) ==> T[x]);
axiom(forall S:[Ref]bool, T:[Ref]bool :: {Subset(S,T)} Subset(S,T) || (exists x:Ref :: S[x] && !T[x]));


////////////////////
// Between predicate
////////////////////
function Btwn(f: [Ref]Ref, x: Ref, y: Ref, z: Ref) returns (bool);
function ReachW(f: [Ref]Ref, x: Ref, y: Ref, z: Ref) returns (bool);


//////////////////////////
// Between set constructor
//////////////////////////
function BtwnSet(f: [Ref]Ref, x: Ref, z: Ref) returns ([Ref]bool);

////////////////////////////////////////////////////
// axioms relating Btwn and BtwnSet
////////////////////////////////////////////////////
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {BtwnSet(f, x, z)[y]} BtwnSet(f, x, z)[y] <==> Btwn(f, x, y, z));
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {Btwn(f, x, y, z), BtwnSet(f, x, z)} Btwn(f, x, y, z) ==> BtwnSet(f, x, z)[y]);
axiom(forall f: [Ref]Ref, x: Ref, z: Ref :: {BtwnSet(f, x, z)} Btwn(f, x, x, x));
axiom(forall f: [Ref]Ref, x: Ref, z: Ref :: {BtwnSet(f, x, z)} Btwn(f, z, z, z));


//////////////////////////
// Axioms for Btwn
//////////////////////////

// reflexive
axiom(forall f: [Ref]Ref, x: Ref :: Btwn(f, x, x, x));

// step
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, w:Ref :: {Btwn(f, y, z, w), f[x]} Btwn(f, x, f[x], f[x]));

// reach
axiom(forall f: [Ref]Ref, x: Ref, y: Ref :: {f[x], Btwn(f, x, y, y)} Btwn(f, x, y, y) ==> x == y || Btwn(f, x, f[x], y));

// cycle
axiom(forall f: [Ref]Ref, x: Ref, y:Ref :: {f[x], Btwn(f, x, y, y)} f[x] == x && Btwn(f, x, y, y) ==> x == y);

// sandwich
axiom(forall f: [Ref]Ref, x: Ref, y: Ref :: {Btwn(f, x, y, x)} Btwn(f, x, y, x) ==> x == y);

// order1
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {Btwn(f, x, y, y), Btwn(f, x, z, z)} Btwn(f, x, y, y) && Btwn(f, x, z, z) ==> Btwn(f, x, y, z) || Btwn(f, x, z, y));

// order2
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {Btwn(f, x, y, z)} Btwn(f, x, y, z) ==> Btwn(f, x, y, y) && Btwn(f, y, z, z));

// transitive1
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {Btwn(f, x, y, y), Btwn(f, y, z, z)} Btwn(f, x, y, y) && Btwn(f, y, z, z) ==> Btwn(f, x, z, z));

// transitive2
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, w: Ref :: {Btwn(f, x, y, z), Btwn(f, y, w, z)} Btwn(f, x, y, z) && Btwn(f, y, w, z) ==> Btwn(f, x, y, w) && Btwn(f, x, w, z));

// transitive3
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, w: Ref :: {Btwn(f, x, y, z), Btwn(f, x, w, y)} Btwn(f, x, y, z) && Btwn(f, x, w, y) ==> Btwn(f, x, w, z) && Btwn(f, w, y, z));

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.
// It cannot be proved using the rest of the axioms.
axiom(forall f: [Ref]Ref, u:Ref, x: Ref :: {Btwn(f, u, x, x)} Btwn(f, u, x, x) ==> Btwn(f, u, u, x));

// relation between ReachW and Btwn
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {ReachW(f, x, y, z)} ReachW(f, x, y, z) <==> (Btwn(f, x, y, z) || (Btwn(f, x, y, y) && !Btwn(f, x, z, z))));
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {Btwn(f, x, y, z)} Btwn(f, x, y, z) <==> (ReachW(f, x, y, z) && ReachW(f, x, z, z)));

// update
axiom(forall f: [Ref]Ref, u: Ref, v: Ref, x: Ref, p: Ref, q: Ref :: {ReachW(f[p := q], u, v, x)} ReachW(f[p := q], u, v, x) <==> ((ReachW(f, u, v, p) && ReachW(f, u, v, x)) || (ReachW(f, u, p, x) && p != x && ReachW(f, q, v, p) && ReachW(f, q, v, x))));

axiom (forall f: [Ref]Ref, p: Ref, q: Ref, u: Ref, w: Ref :: {BtwnSet(f[p := q], u, w)} ReachW(f, u, w, p) ==> Equal(BtwnSet(f[p := q], u, w), BtwnSet(f, u, w)));
axiom (forall f: [Ref]Ref, p: Ref, q: Ref, u: Ref, w: Ref :: {BtwnSet(f[p := q], u, w)} p != w && ReachW(f, u, p, w) && ReachW(f, q, w, p) ==> Equal(BtwnSet(f[p := q], u, w), Union(BtwnSet(f, u, p), BtwnSet(f, q, w))));
axiom (forall f: [Ref]Ref, p: Ref, q: Ref, u: Ref, w: Ref :: {BtwnSet(f[p := q], u, w)} ReachW(f, u, w, p) || (p != w && ReachW(f, u, p, w) && ReachW(f, q, w, p)) || Equal(BtwnSet(f[p := q], u, w), Empty()));


// ---------- Shared state and invariant

type Key;

// Fields:
var {:layer 0, 1} next: [Ref]Ref;
var {:layer 0, 1} data: [Ref]Key;

var {:linear "FP"} {:layer 0, 1} queueFP: [Ref]bool;  // TODO make layer 1,1 and intro actions to modify?
var {:linear "FP"} {:layer 0, 1} usedFP: [Ref]bool;

var {:layer 0, 1} head: Ref;
var {:layer 0, 1} tail: Ref;
var {:layer 0, 1} start: Ref; // The first head. To define usedFP


// Abstract state
var {:layer 1,2} absRefs: [int]Ref;  // connection between abstract and concrete


function {:inline} Inv(queueFP: [Ref]bool, usedFP: [Ref]bool, start: Ref,
    head: Ref, tail: Ref, next: [Ref]Ref, data: [Ref]Key,
    lin: SeqInvoc, vis: [Invoc]SetInvoc, absRefs: [int]Ref,
    called: [Invoc]bool, returned: [Invoc]bool) : bool
{
  // There is a list from head to null
  Btwn(next, head, head, null)
  && (forall x: Ref :: {queueFP[x]}{Btwn(next, head, x, null)}
    queueFP[x] <==> (Btwn(next, head, x, null) && x != null))
  // Tail is on that list
  && Btwn(next, head, tail, null) && tail != null
  // There is also a list from start to head // TODO try just lseg(c, head)
  && Btwn(next, start, start, head)
  && (forall x: Ref :: {usedFP[x]}{Btwn(next, start, x, head)}
    usedFP[x] <==> (Btwn(next, start, x, head) && x != head))
  // Relate abstract state to concrete state:
  && (forall i: int :: {absRefs[i]}
    i < 0 || Queue.stateTail(Queue.ofSeq(lin)) < i <==> absRefs[i] == null)
  && absRefs[Queue.stateHead(Queue.ofSeq(lin))] == head
  && (forall i: int :: {next[absRefs[i]]} absRefs[i + 1] == next[absRefs[i]])
  && (forall i: int :: {Queue.stateArray(Queue.ofSeq(lin))[i], data[absRefs[i]]}
    Queue.stateArray(Queue.ofSeq(lin))[i] == data[absRefs[i]])
  && (forall y: Ref :: {Btwn(next, head, y, null), next[y]}
    Btwn(next, head, y, null) && next[y] == null
    ==> y == absRefs[Queue.stateTail(Queue.ofSeq(lin))])
  // Used to infer that invocations don't modify vis after they've returned
  && (forall n1, n2 : Invoc :: called[n1] && hb(n2, n1) ==> returned[n2])
  // To establish precondition of intro_writeLin
  && (forall n: Invoc :: returned[n] ==> Seq_elem(n, lin))
}

function {:inline} inProgress(called: [Invoc]bool, returned: [Invoc]bool, this: Invoc) : bool
{
  called[this] && !returned[this]
}


// ---------- Primitives for manipulating global state

procedure {:atomic} {:layer 1} readHead_atomic() returns (x: Ref)
{ x := head; }

procedure {:yields} {:layer 0} {:refines "readHead_atomic"} readHead() returns (x: Ref);

procedure {:atomic} {:layer 1} readTail_atomic() returns (x: Ref)
{ x := tail; }

procedure {:yields} {:layer 0} {:refines "readTail_atomic"} readTail() returns (x: Ref);

procedure {:atomic} {:layer 1} casTail_atomic(ole: Ref, new: Ref) returns (b: bool)
  modifies tail;
{
  if (tail == ole) {
    tail := new;
    b := true;
  } else {
    b := false;
  }
}

procedure {:yields} {:layer 0} {:refines "casTail_atomic"}
  casTail(ole: Ref, new: Ref) returns (b: bool);

procedure {:atomic} {:layer 1} readNext_atomic(x: Ref) returns (y: Ref)
{
  assert queueFP[x] || usedFP[x];
  y := next[x];
}

procedure {:yields} {:layer 0} {:refines "readNext_atomic"} readNext(x: Ref) returns (y: Ref);

procedure {:atomic} {:layer 1} readData_atomic(x: Ref) returns (k: Key)
{
  assert queueFP[x] || usedFP[x];
  k := data[x];
}

procedure {:yields} {:layer 0} {:refines "readData_atomic"} readData(x: Ref) returns (k: Key);

procedure {:atomic} {:layer 1} writeNext_atomic(x: Ref, y: Ref, {:linear "FP"} FP:[Ref]bool)
  modifies next;
{
  assert FP[x];
  next := next[x := y];
}

procedure {:yields} {:layer 0} {:refines "writeNext_atomic"}
  writeNext(x: Ref, y: Ref, {:linear "FP"} FP:[Ref]bool);

procedure {:atomic} {:layer 1} casNextTransfer_atomic(x: Ref, oldVal: Ref,
    newVal: Ref, {:linear_in "FP"} inFP:[Ref]bool)
  returns (b: bool, {:linear "FP"} outFP:[Ref]bool)
  modifies next, queueFP;
{
  assert inFP[newVal];
  if (next[x] == oldVal) {
    next := next[x := newVal];
    outFP := emptySet;
    queueFP := queueFP[newVal := true];
    b := true;
  } else {
    outFP := inFP;
    b := false;
  }
}

procedure {:yields} {:layer 0} {:refines "casNextTransfer_atomic"}
  casNextTransfer(x: Ref, oldVal: Ref, newVal: Ref, {:linear_in "FP"} inFP:[Ref]bool)
  returns (b: bool, {:linear "FP"} outFP:[Ref]bool);

procedure {:atomic} {:layer 1} casHeadTransfer_atomic(oldVal: Ref, newVal: Ref) returns (b: bool)
  modifies head, usedFP, queueFP;
{
  if (oldVal == head) {
    head := newVal;
    usedFP[oldVal] := true;
    queueFP := queueFP[oldVal := false];
    b := true;
  }
  else {
    b := false;
  }
}

procedure {:yields} {:layer 0} {:refines "casHeadTransfer_atomic"}
  casHeadTransfer(oldVal: Ref, newVal: Ref) returns (b: bool);


// ---------- Primitives for manipulating logical/abstract state

// procedure {:layer 1} {:inline 1} intro_writeAbs(k: Key, x: Ref)
//   modifies absRefs;
// {
//   absRefs[absTail] := x;
// }

// procedure {:layer 1} {:inline 1} intro_incrHead()
//   modifies absHead;
// {
//   absHead := absHead + 1;
// }

// procedure {:layer 1} {:inline 1} intro_incrTail()
//   modifies absTail;
// {
//   absTail := absTail + 1;
// }


// ---------- Introduction actions:

procedure {:layer 1} intro_readLin() returns (s: SetInvoc)
  ensures {:layer 1} s == Set_ofSeq(lin);
{
  s := Set_ofSeq(lin);
}

procedure {:layer 1} intro_write_vis(n: Invoc, s: SetInvoc)
  modifies vis;
  ensures {:layer 1} vis == old(vis)[n := s];
{
  vis[n] := s;
}

procedure {:layer 1} {:inline 1} intro_writeLin(n: Invoc)
  // To show that linearization is consistent with happens-before
  requires {:layer 1} (forall n1 : Invoc :: hb(n1, n) ==> Seq_elem(n1, lin));
  modifies lin;
{
  lin := Seq_append(lin, n);
}

// Special call and return actions

procedure {:atomic} {:layer 1} spec_call_spec(m: Method, k: Key)
  returns ({:linear "this"} this: Invoc)
  modifies called, returned;
{
  assume m == invoc_m(this) && k == invoc_k(this);
  // everything before this has returned
  assume (forall n1: Invoc :: hb(n1, this) ==> returned[n1]);
  // this has not been called or returned yet
  assume (!called[this] && !returned[this]);
  called[this] := true;
}
procedure {:yields} {:layer 0} {:refines "spec_call_spec"}
  spec_call(m: Method, k: Key) returns ({:linear "this"} this: Invoc);

procedure {:atomic} {:layer 1} spec_return_spec({:linear "this"} this: Invoc)
  modifies returned;
{
  returned[this] := true;
}
procedure {:yields} {:layer 0} {:refines "spec_return_spec"}
  spec_return({:linear "this"} this: Invoc);


// ---------- queue methods:

procedure {:atomic} {:layer 2} atomic_pop() returns (k: Key)
  modifies lin, vis;
{
  var {:linear "this"} this: Invoc; var my_vis: SetInvoc;
  assume Queue.pop == invoc_m(this);

  // Get satisfies its functional spec  // TODO check how Michael did this
  assume k == Queue.stateArray(Queue.ofSeq(lin))[Queue.stateHead(Queue.ofSeq(lin))];

  lin := Seq_append(lin, this);
  vis[this] := my_vis;
  // Get is complete -- TODO make predicate  // TODO only writes in lin?
  assume my_vis == Set_ofSeq(lin);
}

procedure {:yields} {:layer 1} {:refines "atomic_pop"} pop() returns (k: Key)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
{
  var {:linear "this"} this: Invoc;
  var {:layer 1} my_vis: SetInvoc;
  var g: bool;
  var h, t, hn: Ref;

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);

  call this := spec_call(Queue.pop, k);
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned) && inProgress(called, returned, this);

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned) && inProgress(called, returned, this);
  while (true)
    invariant {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned) && inProgress(called, returned, this);
  {
    call h := readHead();
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned) && inProgress(called, returned, this);
    assert {:layer 1} h == head || usedFP[h];

    call t := readTail();
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned) && inProgress(called, returned, this);
    assert {:layer 1} h == head || usedFP[h];
    assert {:layer 1} (h == head && h != t ==> head != tail);

    if (h != t) {
      call hn := readNext(h);
      yield;
      assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned) && inProgress(called, returned, this);
      assert {:layer 1} h == head || usedFP[h];
      assert {:layer 1} (h == head && h != t ==> head != tail && hn == next[head]);

      call k := readData(h);
      yield;
      assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned) && inProgress(called, returned, this);
      assert {:layer 1} h == head || usedFP[h];
      assert {:layer 1} (h == head && h != t ==> head != tail && hn == next[head]);
      assert {:layer 1} data[h] == k;

      call g := casHeadTransfer(h, hn);
      if (g) {
        // Linearization point. TODO
        call intro_writeLin(this);
        call my_vis := intro_readLin();
        call intro_write_vis(this, my_vis);

  assert {:layer 1} Btwn(next, head, head, null);
  assert {:layer 1} (forall x: Ref :: {queueFP[x]}{Btwn(next, head, x, null)}
    queueFP[x] <==> (Btwn(next, head, x, null) && x != null));
  // Tail is on that list
  assert {:layer 1} Btwn(next, head, tail, null) && tail != null;
  // There is also a list from start to head // TODO try just lseg(c, head)
  assert {:layer 1} Btwn(next, start, start, head);
  assert {:layer 1} (forall x: Ref :: {usedFP[x]}{Btwn(next, start, x, head)}
    usedFP[x] <==> (Btwn(next, start, x, head) && x != head));
  // Relate abstract state to concrete state:
  assert {:layer 1} (forall i: int :: {absRefs[i]}
    i < 0 || Queue.stateTail(Queue.ofSeq(lin)) < i <==> absRefs[i] == null);
  assert {:layer 1} absRefs[Queue.stateHead(Queue.ofSeq(lin))] == head;
  assert {:layer 1} (forall i: int :: {next[absRefs[i]]} absRefs[i + 1] == next[absRefs[i]]);
  assert {:layer 1} (forall i: int :: {Queue.stateArray(Queue.ofSeq(lin))[i], data[absRefs[i]]}
    Queue.stateArray(Queue.ofSeq(lin))[i] == data[absRefs[i]]);
  assert {:layer 1} (forall y: Ref :: {Btwn(next, head, y, null), next[y]}
    Btwn(next, head, y, null) && next[y] == null
    ==> y == absRefs[Queue.stateTail(Queue.ofSeq(lin))]);
  // Used to infer that invocations don't modify vis after they've returned
  assert {:layer 1} (forall n1, n2 : Invoc :: called[n1] && hb(n2, n1) ==> returned[n2]);
  // To establish precondition of intro_writeLin
  assert {:layer 1} (forall n: Invoc :: returned[n] ==> Seq_elem(n, lin));
        break;
      }
    }  // TODO return EMPTY?
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned) && inProgress(called, returned, this);
  }
  yield;
  assert {:expand} {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
}

/*

procedure {:atomic} {:layer 2} atomic_push(k: Key, x: Ref, {:linear_in "FP"} xFP: [Ref]bool)
  // modifies absArray, absTail, absRefs;
{
}

procedure {:yields} {:layer 1} {:refines "atomic_push"} push(k: Key, x: Ref,
    {:linear_in "FP"} xFP: [Ref]bool)
  requires {:layer 1} xFP[x] && next[x] == null && data[x] == k;  // TODO alloc x with k
  requires {:layer 1} !Btwn(next, head, x, null);  // TODO get from linearity
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
{
  var t, tn: Ref;
  var g: bool;
  var {:linear "FP"} tFP: [Ref]bool;

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
  assert {:layer 1} !Btwn(next, head, x, null);
  assert {:layer 1} xFP[x] && next[x] == null && data[x] == k;
  tFP := xFP;
  while (true)
    invariant {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
    invariant {:layer 1} !Btwn(next, head, x, null);
    invariant {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k;
  {
    call t := readTail();
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k;
    assert {:layer 1} t != null && (queueFP[t] || usedFP[t]);
    assert {:layer 1} next[t] == null ==> queueFP[t];

    call tn := readNext(t);
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k;
    assert {:layer 1} t != null && (queueFP[t] || usedFP[t]);
    assert {:layer 1} next[t] == null ==> queueFP[t];
    assert {:layer 1} tn != null ==> tn == next[t];

    if (tn == null) {
      call g, tFP := casNextTransfer(t, tn, x, tFP);
      if (g) {
        // Linearization point. TODO
        // call intro_incrTail();
        call intro_writeAbs(k, x);
        break;
      }
    } else {
      call g := casTail(t, tn);
    }
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k;
  }
  yield;
  assert {:expand} {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
}


procedure {:atomic} {:layer 2} atomic_size() returns (s: int)
{}

// Size invariant: s == indexOf[c] - old(absHead)
procedure {:yields} {:layer 1} {:refines "atomic_size"} size() returns (s: int)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
{
  var c: Ref;

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);

  s := 0;
  call c := readHead();

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
  assert {:layer 1} (usedFP[c] || queueFP[c]);

  while (c != null)
    invariant {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
    invariant {:layer 1} (usedFP[c] || queueFP[c] || c == null);
  {
    s := s + 1;
    call c := readNext(c);
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
    assert {:layer 1} (usedFP[c] || queueFP[c] || c == null);
  }
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, lin, vis, absRefs, called, returned);
  return;
}

*/