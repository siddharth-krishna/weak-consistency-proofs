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


// ---------- Axioms of the queue ADT

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

type Ref;
const null: Ref;

type Heap;
function dom(Heap): [Ref]bool;
function next(Heap): [Ref]Ref;
function data(Heap): [Ref]int;
function {:builtin "MapConst"} MapConstLocBool(bool) : [Ref]bool;

function {:inline} {:linear "FP"} FPCollector(FP: [Ref]bool) : [Ref]bool
{ FP }

function EmptyLmap(): (Heap);
axiom (dom(EmptyLmap()) == MapConstLocBool(false));

function Add(h: Heap, l: Ref, v: Ref): (Heap);
axiom (forall h: Heap, l: Ref, v: Ref :: dom(Add(h, l, v)) == dom(h)[l:=true] && next(Add(h, l, v)) == next(h)[l := v]);

function Remove(h: Heap, l: Ref): (Heap);
axiom (forall h: Heap, l: Ref :: dom(Remove(h, l)) == dom(h)[l:=false] && next(Remove(h, l)) == next(h));


// ---------- Reachability, between, and associated theories

// Predicates used to control the triggers on the below axioms
function known(x: Ref) : bool;
function knownF(f: [Ref]Ref) : bool;
axiom(forall x: Ref :: {known(x)} known(x));
axiom(forall f: [Ref]Ref :: {knownF(f)} knownF(f));

 
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
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} BtwnSet(f, x, z)[y] <==> Btwn(f, x, y, z));
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} Btwn(f, x, y, z) ==> BtwnSet(f, x, z)[y]);
axiom(forall f: [Ref]Ref, x: Ref :: {knownF(f), known(x)} Btwn(f, x, x, x));
axiom(forall f: [Ref]Ref, x: Ref, z: Ref :: {BtwnSet(f, x, z)} Btwn(f, z, z, z));


//////////////////////////
// Axioms for Btwn
//////////////////////////

// reflexive
axiom(forall f: [Ref]Ref, x: Ref :: Btwn(f, x, x, x));

// step
axiom(forall f: [Ref]Ref, x: Ref :: {f[x]} Btwn(f, x, f[x], f[x]));

// reach
axiom(forall f: [Ref]Ref, x: Ref, y: Ref :: {f[x], known(y)} Btwn(f, x, y, y) ==> x == y || Btwn(f, x, f[x], y));

// cycle
axiom(forall f: [Ref]Ref, x: Ref, y:Ref :: {f[x], known(y)} f[x] == x && Btwn(f, x, y, y) ==> x == y);

// sandwich
axiom(forall f: [Ref]Ref, x: Ref, y: Ref :: {knownF(f), known(x), known(y)} Btwn(f, x, y, x) ==> x == y);

// order1
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} Btwn(f, x, y, y) && Btwn(f, x, z, z) ==> Btwn(f, x, y, z) || Btwn(f, x, z, y));

// order2
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} Btwn(f, x, y, z) ==> Btwn(f, x, y, y) && Btwn(f, y, z, z));

// transitive1
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} Btwn(f, x, y, y) && Btwn(f, y, z, z) ==> Btwn(f, x, z, z));

// transitive2
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, w: Ref :: {knownF(f), known(x), known(y), known(z), known(w)} Btwn(f, x, y, z) && Btwn(f, y, w, z) ==> Btwn(f, x, y, w) && Btwn(f, x, w, z));

// transitive3
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, w: Ref :: {knownF(f), known(x), known(y), known(z), known(w)} Btwn(f, x, y, z) && Btwn(f, x, w, y) ==> Btwn(f, x, w, z) && Btwn(f, w, y, z));

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.
// It cannot be proved using the rest of the axioms.
axiom(forall f: [Ref]Ref, u:Ref, x: Ref :: {knownF(f), known(x), known(u)} Btwn(f, u, x, x) ==> Btwn(f, u, u, x));

// relation between ReachW and Btwn
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} ReachW(f, x, y, z) <==> (Btwn(f, x, y, z) || (Btwn(f, x, y, y) && !Btwn(f, x, z, z))));
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} Btwn(f, x, y, z) <==> (ReachW(f, x, y, z) && ReachW(f, x, z, z)));

// BWr: grasshopper's update axiom
axiom (forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, u: Ref, v: Ref :: {f[u := v], known(x), known(y), known(z)}
        Btwn(f[u := v], x, y, z) <==>
          (Btwn(f, x, y, z) && ReachW(f, x, z, u))
          || (u != z && ReachW(f, x, u, z) && ReachW(f, v, z, u)
            && (Btwn(f, x, y, u) || Btwn(f, v, y, z))));


// ---------- Logical and concrete shared state

// Visibility per key
var {:layer 1,1} keyvis: [int]SetInvoc;

// Concrete state of implementation
var {:layer 0,1} heap: Heap;
var {:linear "FP"} queue_FP: [Ref]bool;
var {:layer 0,1} head: Ref;
var {:layer 0,1} tail: Ref;


// The invariants
function {:inline} Inv(heap: Heap, head: Ref, tail: Ref, queue_FP: [Ref]bool,
                            lin: SeqInvoc, vis: [Invoc]SetInvoc,
                            called: [Invoc]bool, returned: [Invoc]bool) : bool
{
  Btwn(next(heap), head, head, null) && Btwn(next(heap), head, tail, null)
    && BtwnSet(next(heap), head, null) == queue_FP
    && (forall l: Ref :: known(l) ==> (Btwn(next(heap), head, l, null) ==> l == null || dom(heap)[l]))
    && tail != null
    && known(head) && known(tail) && known(null) && knownF(next(heap))
}

function {:inline} inProgress(called: [Invoc]bool, returned: [Invoc]bool, this: Invoc) : bool
{
  called[this] && !returned[this]
}

// ---------- Primitives/helpers for modifying global state

procedure {:atomic} {:layer 1} read_tail_spec() returns (t: Ref)
{
  t := tail;
}
procedure {:yields} {:layer 0} {:refines "read_tail_spec"}
  read_tail() returns (t: Ref);

procedure {:atomic} {:layer 1} read_next_spec(x: Ref) returns (y: Ref)
{
  assert dom(heap)[x];
  y := next(heap)[x];
  assume known(y);
}
procedure {:yields} {:layer 0} {:refines "read_next_spec"}
  read_next(x: Ref) returns (y: Ref);

procedure {:atomic} {:layer 1} cas_next_spec(x, x_old, x_new: Ref)
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
  assume knownF(next(heap));
}
procedure {:yields} {:layer 0} {:refines "cas_next_spec"}
  cas_next(x, x_old, x_new: Ref) returns (res: bool);

procedure {:atomic} {:layer 1} alloc_spec()
  returns (x: Ref, {:linear "FP"} x_FP: [Ref]bool)
  modifies heap;
{
  assume !dom(heap)[x] && x != null;
  heap := Add(heap, x, null);
  assume x_FP == MapConstLocBool(false)[x := true];
  assume known(x) && knownF(next(heap));
}
procedure {:yields} {:layer 0} {:refines "alloc_spec"}
alloc() returns (x: Ref, {:linear "FP"} x_FP: [Ref]bool);

procedure {:atomic} {:layer 1} cas_tail_spec(t_old, t_new: Ref)
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
procedure {:yields} {:layer 0} {:refines "cas_tail_spec"} cas_tail(t_old, t_new: Ref)
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

procedure {:layer 1} assume_false();
  ensures {:layer 1} false;
  

procedure {:yields} {:layer 1} {:refines "offer_spec"}
  offer(v: int)
  returns (res: bool)
  requires {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
  ensures {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
{
  var t, tn: Ref;
  var b: bool;
  var x: Ref; var {:linear "FP"} x_FP: [Ref]bool;
  yield;
  assert {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
  assert {:layer 1} knownF(next(heap)) && known(x);
  // TODO assume !Btwn(next(heap), head, x, null) && !dom(heap)[x];

  call x, x_FP := alloc();

  assert {:layer 1} BtwnSet(next(heap), head, null) == queue_FP;
  yield;
  assert {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
  assert {:layer 1} !Btwn(next(heap), head, x, null);
  assert {:layer 1} known(x) && x != null && dom(heap)[x] && next(heap)[x] == null;

  while (true)
    invariant {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
    invariant {:layer 1} known(x) && x != null && dom(heap)[x] && next(heap)[x] == null;
    invariant {:layer 1} !Btwn(next(heap), head, x, null);
  {
    call t := read_tail();

    yield; assert {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
    assert {:layer 1} !Btwn(next(heap), head, x, null);
    assert {:layer 1} dom(heap)[x] && next(heap)[x] == null;
    assert {:layer 1} dom(heap)[t] && t != x;
    assert {:layer 1} Btwn(next(heap), head, t, null);

    call assume_false();
    /*

    call tn := read_next(t);

    if (tn == null) {
      yield; assert {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
      assert {:layer 1} !Btwn(next(heap), head, x, null);
      assert {:layer 1} dom(heap)[x] && next(heap)[x] == null;
      assert {:layer 1} dom(heap)[t] && t != x;
      assert {:layer 1} Btwn(next(heap), head, t, null);
      assert {:layer 1} Btwn(next(heap), head, tn, null);

      call b := cas_next(t, tn, x);
      if (b) {
        res := true;
  
        yield; assert {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);  // Not true
        return;
      }
    } else {
      yield; assert {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
      assert {:layer 1} !Btwn(next(heap), head, x, null);
      assert {:layer 1} dom(heap)[x] && next(heap)[x] == null;
      assert {:layer 1} Btwn(next(heap), head, tn, null);

      call b:= cas_tail(t, tn);
    }
    yield; assert {:layer 1} Inv(heap, head, tail, queue_FP, lin, vis, called, returned);
    assert {:layer 1} !Btwn(next(heap), head, x, null);
    assert {:layer 1} dom(heap)[x] && next(heap)[x] == null;
     */
  }
  yield;
}


