// ----------------------------------------
// A simple queue implementation based on the Michael-Scott queue
// Assumes GC, so does not free dequeued nodes
// ----------------------------------------


// ---------- Types of methods and invocations

type Method;

type Invoc;

// Boilerplate stuff for linear variables
function {:builtin "MapConst"} MapConstBool(bool) : [Invoc]bool;
function {:inline} {:linear "this"} TidCollector(x: Invoc) : [Invoc]bool
{
  MapConstBool(false)[x := true]
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


// ---------- Axioms of the map ADT

const unique offer, poll, size: Method;

function invoc_m(n: Invoc) : Method;
function invoc_v(n: Invoc) : int;



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

type Loc;
const null: Loc;

type Heap;
function dom(Heap): [Loc]bool;
function next(Heap): [Loc]Loc;
function data(Heap): [Loc]int;
function {:builtin "MapConst"} MapConstLocBool(bool) : [Loc]bool;

function {:inline} {:linear "FP"} FPCollector(FP: [Loc]bool) : [Loc]bool
{ FP }

function EmptyLmap(): (Heap);
axiom (dom(EmptyLmap()) == MapConstLocBool(false));

function Add(h: Heap, l: Loc, v: Loc): (Heap);
axiom (forall h: Heap, l: Loc, v: Loc :: dom(Add(h, l, v)) == dom(h)[l:=true] && next(Add(h, l, v)) == next(h)[l := v]);

function Remove(h: Heap, l: Loc): (Heap);
axiom (forall h: Heap, l: Loc :: dom(Remove(h, l)) == dom(h)[l:=false] && next(Remove(h, l)) == next(h));


// ---------- Logical and concrete shared state

// Visibility per key
var {:layer 1,1} keyvis: [int]SetInvoc;

// Concrete state of implementation
var {:layer 0,1} heap: Heap;
var {:linear "FP"} queue_FP: [Loc]bool;
var {:layer 0,1} head: Loc;
var {:layer 0,1} tail: Loc;


// The invariants
function {:inline} Inv(heap: Heap, head: Loc, tail: Loc, queue_FP: [Loc]bool,
                            lin: SeqInvoc, vis: [Invoc]SetInvoc,
                            called: [Invoc]bool, returned: [Invoc]bool) : bool
{
  Between(next(heap), head, head, null) && Between(next(heap), head, tail, null)
    && BetweenSet(next(heap), head, null) == queue_FP
    && Subset(queue_FP, Union(Singleton(null), dom(heap)))
    && tail != null
}

function {:inline} inProgress(called: [Invoc]bool, returned: [Invoc]bool, this: Invoc) : bool
{
  called[this] && !returned[this]
}

// ---------- Primitives/helpers for modifying global state

procedure {:atomic} {:layer 1} read_tail_spec() returns (t: Loc)
{
  t := tail;
}
procedure {:yields} {:layer 0} {:refines "read_tail_spec"}
  read_tail() returns (t: Loc);

procedure {:atomic} {:layer 1} read_next_spec(x: Loc) returns (y: Loc)
{
  assert dom(heap)[x];
  y := next(heap)[x];
}
procedure {:yields} {:layer 0} {:refines "read_next_spec"}
  read_next(x: Loc) returns (y: Loc);

procedure {:atomic} {:layer 1} cas_next_spec(x, x_old, x_new: Loc)
  returns (res: bool)
  modifies heap;
{
  assert dom(heap)[x] && queue_FP[x];
  if (next(heap)[x] == x_old) {
    heap := Add(heap, x, x_new);
    res := true;
  } else {
    res := false;
  }
}
procedure {:yields} {:layer 0} {:refines "cas_next_spec"}
  cas_next(x, x_old, x_new: Loc) returns (res: bool);

procedure {:atomic} {:layer 1} alloc_spec()
  returns (x: Loc, {:linear "FP"} x_FP: [Loc]bool)
  modifies heap;
{
  assume !dom(heap)[x];
  heap := Add(heap, x, null);
  assume x_FP == MapConstLocBool(false)[x := true];
}
procedure {:yields} {:layer 0} {:refines "alloc_spec"}
alloc() returns (x: Loc, {:linear "FP"} x_FP: [Loc]bool);

procedure {:atomic} {:layer 1} cas_tail_spec(t_old, t_new: Loc)
  returns (res: bool)
  modifies tail;
{
  if (tail == t_old) {
    tail := t_new;
    res := true;
  } else {
    res := false;
  }
}
procedure {:yields} {:layer 0} {:refines "cas_tail_spec"} cas_tail(t_old, t_new: Loc)
  returns (res: bool);


// ---------- Introduction actions:

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

procedure {:atomic} {:layer 1} spec_call_spec(m: Method, k, v: int)
  returns ({:linear "this"} this: Invoc)
  modifies called, returned;
{
  assume m == invoc_m(this) && v == invoc_v(this);
  // everything before this has returned
  assume (forall n1: Invoc :: hb(n1, this) ==> returned[n1]);
  // this has not been called or returned yet
  assume (!called[this] && !returned[this]);
  called[this] := true;
}
procedure {:yields} {:layer 0} {:refines "spec_call_spec"}
  spec_call(m: Method, k, v: int) returns ({:linear "this"} this: Invoc);

procedure {:atomic} {:layer 1} spec_return_spec({:linear "this"} this: Invoc)
  modifies returned;
{
  returned[this] := true;
}
procedure {:yields} {:layer 0} {:refines "spec_return_spec"}
  spec_return({:linear "this"} this: Invoc);


// ---------- The ADT methods

procedure {:atomic} {:layer 2} offer_spec(v: int)
  returns (res: bool)
  modifies lin, vis;
{
  /*
  var {:linear "this"} this: Invoc;
  var my_vis: SetInvoc;
  assume offer == invoc_m(this) && v == invoc_v(this);
  lin := Seq_append(lin, this);
  vis[this] := my_vis;

  // Offer is complete
  assume my_vis == Set_ofSeq(lin);
   */
  // Offer satisfies its functional spec
  assume res == true; // TODO adt_spec(vis, lin);
}

procedure {:yields} {:layer 1} {:refines "offer_spec"}
  offer(v: int)
  returns (res: bool)
  requires {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
  ensures {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
{
  var t, tn: Loc;
  var b: bool;
  var x: Loc; var {:linear "FP"} x_FP: [Loc]bool;
  yield; assert {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);

  call x, x_FP := alloc();

  yield; assert {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
  assert {:layer 1} !Between(next(heap), head, x, null);
  assert {:layer 1} dom(heap)[x];
  assert {:layer 1} next(heap)[x] == null;

  while (true)
    invariant {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
    invariant {:layer 1} !Between(next(heap), head, x, null);
    invariant {:layer 1} dom(heap)[x] && next(heap)[x] == null;
  {
    call t := read_tail();

    yield; assert {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
    assert {:layer 1} !Between(next(heap), head, x, null);
    assert {:layer 1} dom(heap)[x] && next(heap)[x] == null;
    assert {:layer 1} dom(heap)[t] && t != x;
    assert {:layer 1} Between(next(heap), head, t, null);

    call tn := read_next(t);

    if (tn == null) {
      yield; assert {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
      assert {:layer 1} !Between(next(heap), head, x, null);
      assert {:layer 1} dom(heap)[x] && next(heap)[x] == null;
      assert {:layer 1} dom(heap)[t] && t != x;
      assert {:layer 1} Between(next(heap), head, t, null);
      assert {:layer 1} Between(next(heap), head, tn, null);

      call b := cas_next(t, tn, x);
      if (b) {
        res := true;
  
        yield; assert {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);  // Not true
        return;
      }
    } else {
      yield; assert {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
      assert {:layer 1} !Between(next(heap), head, x, null);
      assert {:layer 1} dom(heap)[x] && next(heap)[x] == null;
      assert {:layer 1} Between(next(heap), head, tn, null);

      call b:= cas_tail(t, tn);
    }
    yield; assert {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
    assert {:layer 1} !Between(next(heap), head, x, null);
    assert {:layer 1} dom(heap)[x] && next(heap)[x] == null;
  }
  yield;
}


// ---------- Reachability, between, and associated theories

function Equal([Loc]bool, [Loc]bool) returns (bool);
function Subset([Loc]bool, [Loc]bool) returns (bool);

function Empty() returns ([Loc]bool);
function Singleton(Loc) returns ([Loc]bool);
function Union([Loc]bool, [Loc]bool) returns ([Loc]bool);

axiom(forall x:Loc :: !Empty()[x]);

axiom(forall x:Loc, y:Loc :: {Singleton(y)[x]} Singleton(y)[x] <==> x == y);
axiom(forall y:Loc :: {Singleton(y)} Singleton(y)[y]);

axiom(forall x:Loc, S:[Loc]bool, T:[Loc]bool :: {Union(S,T)[x]}{Union(S,T),S[x]}{Union(S,T),T[x]} Union(S,T)[x] <==> S[x] || T[x]);

axiom(forall S:[Loc]bool, T:[Loc]bool :: {Equal(S,T)} Equal(S,T) <==> Subset(S,T) && Subset(T,S));
axiom(forall x:Loc, S:[Loc]bool, T:[Loc]bool :: {S[x],Subset(S,T)}{T[x],Subset(S,T)} S[x] && Subset(S,T) ==> T[x]);
axiom(forall S:[Loc]bool, T:[Loc]bool :: {Subset(S,T)} Subset(S,T) || (exists x:Loc :: S[x] && !T[x]));

////////////////////
// Between predicate
////////////////////
function Between(f: [Loc]Loc, x: Loc, y: Loc, z: Loc) returns (bool);
function Avoiding(f: [Loc]Loc, x: Loc, y: Loc, z: Loc) returns (bool);


//////////////////////////
// Between set constructor
//////////////////////////
function BetweenSet(f: [Loc]Loc, x: Loc, z: Loc) returns ([Loc]bool);

////////////////////////////////////////////////////
// axioms relating Between and BetweenSet
////////////////////////////////////////////////////
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {BetweenSet(f, x, z)[y]} BetweenSet(f, x, z)[y] <==> Between(f, x, y, z));
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {Between(f, x, y, z), BetweenSet(f, x, z)} Between(f, x, y, z) ==> BetweenSet(f, x, z)[y]);
axiom(forall f: [Loc]Loc, x: Loc, z: Loc :: {BetweenSet(f, x, z)} Between(f, x, x, x));
axiom(forall f: [Loc]Loc, x: Loc, z: Loc :: {BetweenSet(f, x, z)} Between(f, z, z, z));


//////////////////////////
// Axioms for Between
//////////////////////////

// reflexive
axiom(forall f: [Loc]Loc, x: Loc :: Between(f, x, x, x));

// step
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc, w:Loc :: {Between(f, y, z, w), f[x]} Between(f, x, f[x], f[x]));

// reach
axiom(forall f: [Loc]Loc, x: Loc, y: Loc :: {f[x], Between(f, x, y, y)} Between(f, x, y, y) ==> x == y || Between(f, x, f[x], y));

// cycle
axiom(forall f: [Loc]Loc, x: Loc, y:Loc :: {f[x], Between(f, x, y, y)} f[x] == x && Between(f, x, y, y) ==> x == y);

// sandwich
axiom(forall f: [Loc]Loc, x: Loc, y: Loc :: {Between(f, x, y, x)} Between(f, x, y, x) ==> x == y);

// order1
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {Between(f, x, y, y), Between(f, x, z, z)} Between(f, x, y, y) && Between(f, x, z, z) ==> Between(f, x, y, z) || Between(f, x, z, y));

// order2
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {Between(f, x, y, z)} Between(f, x, y, z) ==> Between(f, x, y, y) && Between(f, y, z, z));

// transitive1
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {Between(f, x, y, y), Between(f, y, z, z)} Between(f, x, y, y) && Between(f, y, z, z) ==> Between(f, x, z, z));

// transitive2
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc, w: Loc :: {Between(f, x, y, z), Between(f, y, w, z)} Between(f, x, y, z) && Between(f, y, w, z) ==> Between(f, x, y, w) && Between(f, x, w, z));

// transitive3
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc, w: Loc :: {Between(f, x, y, z), Between(f, x, w, y)} Between(f, x, y, z) && Between(f, x, w, y) ==> Between(f, x, w, z) && Between(f, w, y, z));

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.
// It cannot be proved using the rest of the axioms.
axiom(forall f: [Loc]Loc, u:Loc, x: Loc :: {Between(f, u, x, x)} Between(f, u, x, x) ==> Between(f, u, u, x));

// relation between Avoiding and Between
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {Avoiding(f, x, y, z)} Avoiding(f, x, y, z) <==> (Between(f, x, y, z) || (Between(f, x, y, y) && !Between(f, x, z, z))));
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {Between(f, x, y, z)} Between(f, x, y, z) <==> (Avoiding(f, x, y, z) && Avoiding(f, x, z, z)));

// update
axiom(forall f: [Loc]Loc, u: Loc, v: Loc, x: Loc, p: Loc, q: Loc :: {Avoiding(f[p := q], u, v, x)} Avoiding(f[p := q], u, v, x) <==> ((Avoiding(f, u, v, p) && Avoiding(f, u, v, x)) || (Avoiding(f, u, p, x) && p != x && Avoiding(f, q, v, p) && Avoiding(f, q, v, x))));

axiom (forall f: [Loc]Loc, p: Loc, q: Loc, u: Loc, w: Loc :: {BetweenSet(f[p := q], u, w)} Avoiding(f, u, w, p) ==> Equal(BetweenSet(f[p := q], u, w), BetweenSet(f, u, w)));
axiom (forall f: [Loc]Loc, p: Loc, q: Loc, u: Loc, w: Loc :: {BetweenSet(f[p := q], u, w)} p != w && Avoiding(f, u, p, w) && Avoiding(f, q, w, p) ==> Equal(BetweenSet(f[p := q], u, w), Union(BetweenSet(f, u, p), BetweenSet(f, q, w))));
axiom (forall f: [Loc]Loc, p: Loc, q: Loc, u: Loc, w: Loc :: {BetweenSet(f[p := q], u, w)} Avoiding(f, u, w, p) || (p != w && Avoiding(f, u, p, w) && Avoiding(f, q, w, p)) || Equal(BetweenSet(f[p := q], u, w), Empty()));
