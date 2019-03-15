// ----------------------------------------
// A simple queue implementation
// based on the Michael-Scott queue.
// Assumes GC, so does not free dequeued nodes.
// Also uses the simplified heap encoding from CIVL's Treiber example.
//
// Use options -noinfer -typeEncoding:m -useArrayTheory
// ----------------------------------------

type Ref;
const null: Ref;

type Heap;
function {:linear "Node"} dom(Heap): [Ref]bool;
function next(Heap): [Ref]Ref;
function {:builtin "MapConst"} MapConstBool(bool) : [Ref]bool;

function EmptyHeap(): (Heap);
axiom (dom(EmptyHeap()) == MapConstBool(false));

function Add(h: Heap, l: Ref, v: Ref): (Heap);
axiom (forall h: Heap, l: Ref, v: Ref :: dom(Add(h, l, v)) == dom(h)[l:=true] && next(Add(h, l, v)) == next(h)[l := v]);

function Remove(h: Heap, l: Ref): (Heap);
axiom (forall h: Heap, l: Ref :: dom(Remove(h, l)) == dom(h)[l:=false] && next(Remove(h, l)) == next(h));

// Linearity stuff:

function {:inline} {:linear "Node"} NodeSetCollector(x: [Ref]bool) : [Ref]bool
{
  x
}


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

var {:linear "Node"} {:layer 0,2} queue: Heap;
var {:linear "Node"} {:layer 0,2} Used: [Ref]bool;

var {:layer 0,2} head: Ref;
var {:layer 0,2} tail: Ref;


function {:inline} Inv(queue: Heap, head: Ref, tail: Ref) : (bool)
{
  Btwn(next(queue), head, head, null)
    && Btwn(next(queue), head, tail, null)
    && Equal(BtwnSet(next(queue), head, null),
             Union(Singleton(null), dom(queue)))
    && tail != null
}


// ---------- Primitives for manipulating ghost state

procedure {:atomic} {:layer 1} AtomicReadhead() returns (v:Ref)
{ v := head; }

procedure {:yields} {:layer 0} {:refines "AtomicReadhead"} Readhead() returns (v:Ref);

procedure {:atomic} {:layer 1} AtomicReadtail() returns (v:Ref)
{ v := tail; }

procedure {:yields} {:layer 0} {:refines "AtomicReadtail"} Readtail() returns (v:Ref);

procedure {:atomic} {:layer 1} AtomicLoad(i:Ref) returns (v:Ref)
{
  assert dom(queue)[i] || Used[i];
  if (dom(queue)[i]) {
    v := next(queue)[i];
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicLoad"} Load(i:Ref) returns (v:Ref);

procedure {:both} {:layer 1} AtomicStore({:linear_in "Node"} l_in:Heap, i:Ref, v:Ref) returns ({:linear "Node"} l_out:Heap)
{ assert dom(l_in)[i]; l_out := Add(l_in, i, v); }

procedure {:yields} {:layer 0} {:refines "AtomicStore"} Store({:linear_in "Node"} l_in:Heap, i:Ref, v:Ref) returns ({:linear "Node"} l_out:Heap);


procedure {:atomic} {:layer 1} AtomicTransferToqueue(t: Ref, oldVal: Ref,
    newVal: Ref, {:linear_in "Node"} l_in:Heap)
  returns (r: bool, {:linear "Node"} l_out:Heap)
  modifies queue;
{
  assert dom(l_in)[newVal];
  if (next(queue)[t] == oldVal) {
    queue := Add(queue, t, newVal);
    l_out := EmptyHeap();
    queue := Add(queue, newVal, next(l_in)[newVal]);
    r := true;
  } else {
    l_out := l_in;
    r := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicTransferToqueue"}
  TransferToqueue(t: Ref, oldVal: Ref, newVal: Ref,
                  {:linear_in "Node"} l_in:Heap)
  returns (r: bool, {:linear "Node"} l_out:Heap);

procedure {:atomic} {:layer 1} AtomicTransferFromqueue(oldVal: Ref, newVal: Ref) returns (r: bool)
  modifies head, Used, queue;
{
  if (oldVal == head) {
    head := newVal;
    Used[oldVal] := true;
    queue := Remove(queue, oldVal);
    r := true;
  }
  else {
    r := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicTransferFromqueue"} TransferFromqueue(oldVal: Ref, newVal: Ref) returns (r: bool);


// ---------- queue methods:

procedure {:atomic} {:layer 2} atomic_pop() returns (t: Ref)
  modifies Used, head, queue;
{
  assume head != null;
  t := head;
  Used[t] := true;
  head := next(queue)[t];
  queue := Remove(queue, t);
}

procedure {:yields} {:layer 1} {:refines "atomic_pop"} pop() returns (h: Ref)
requires {:layer 1} Inv(queue, head, tail);
ensures {:layer 1} Inv(queue, head, tail);
{
  var g: bool;
  var t, x: Ref;

  yield;
  assert {:layer 1} Inv(queue, head, tail);
  while (true)
    invariant {:layer 1} Inv(queue, head, tail);
  {
    call h := Readhead();
    yield;
    assert {:layer 1} Inv(queue, head, tail);
    assert {:layer 1} h == head || Used[h];

    call t := Readtail();
    yield;
    assert {:layer 1} Inv(queue, head, tail);
    assert {:layer 1} h == head || Used[h];
    assert {:layer 1} (h == head && h != t ==> head != tail);

    if (h != t) {
      call x := Load(h);
      yield;
      assert {:layer 1} Inv(queue, head, tail);
      assert {:layer 1} h == head || Used[h];
      assert {:layer 1} (h == head && h != t ==> x == next(queue)[head]);
      assert {:layer 1} (h == head && h != t ==> head != tail);

      call g := TransferFromqueue(h, x);
      if (g) {
        break;
      }
    }
    yield;
    assert {:layer 1} Inv(queue, head, tail);
  }
  yield;
  assert {:expand} {:layer 1} Inv(queue, head, tail);
}


procedure {:atomic} {:layer 2} atomic_push(x: Ref,
 {:linear_in "Node"} x_Heap: Heap)
 modifies queue, tail;
{
  if (next(queue)[tail] == null) {
    queue := Add(queue, tail, x);
    queue := Add(queue, x, null);
  }
  // tail := x;
}

procedure {:yields} {:layer 1} {:refines "atomic_push"} push(x: Ref, {:linear_in "Node"} x_Heap: Heap)
  requires {:layer 1} x != null && dom(x_Heap)[x] && next(x_Heap)[x] == null;
  requires {:layer 1} Inv(queue, head, tail);
  ensures {:layer 1} Inv(queue, head, tail);
{
  var t, tn: Ref;
  var g: bool;
  var {:linear "Node"} t_Heap: Heap;

  yield;
  assert {:layer 1} Inv(queue, head, tail);
  // TODO CONTINUE: debug non-interference for this:
  // assert {:layer 1} !Btwn(next(queue), head, x, null);
  t_Heap := x_Heap;
  while (true)
    invariant {:layer 1} dom(t_Heap) == dom(x_Heap);
    invariant {:layer 1} next(t_Heap)[x] == null; // TODO needed?
    // invariant {:layer 1} !Btwn(next(queue), head, x, null);
    invariant {:layer 1} Inv(queue, head, tail);
  {
    call t := Readtail();
    yield;
    assert {:layer 1} Inv(queue, head, tail);
    assert {:layer 1} dom(t_Heap) == dom(x_Heap);
    assert {:layer 1} next(t_Heap)[x] == null;  // TODO needed?
    // assert {:layer 1} !Btwn(next(queue), head, x, null);
    assert {:layer 1} t != null && (Btwn(next(queue), head, t, null)
      || Used[t]);
    assert {:layer 1} next(queue)[t] == null ==> t == tail;

    call tn := Load(t);
    yield;
    assert {:layer 1} Inv(queue, head, tail);
    assert {:layer 1} dom(t_Heap) == dom(x_Heap);
    assert {:layer 1} next(t_Heap)[x] == null;
    // assert {:layer 1} !Btwn(next(queue), head, x, null);
    assert {:layer 1} t != null && (Btwn(next(queue), head, t, null)
      || Used[t]);
    assert {:layer 1} next(queue)[t] == null ==> t == tail;

    if (tn == null) {
      // call _assume_not_btwn(x);
      call g, t_Heap := TransferToqueue(t, tn, x, t_Heap);
      if (g) {
        break;
      }
    } // TODO else cas tail
    yield;
    assert {:layer 1} dom(t_Heap) == dom(x_Heap);
    // assert {:layer 1} !Btwn(next(queue), head, x, null);
    assert {:layer 1} Inv(queue, head, tail);
  }
  yield;
  assert {:expand} {:layer 1} Inv(queue, head, tail);
}

procedure {:layer 1} _assume_not_btwn(x: Ref);
  ensures {:layer 1} !Btwn(next(queue), head, x, null);
  
/*
procedure {:atomic} {:layer 2} atomic_size() returns (x: int)
{}

procedure {:yields} {:layer 1} {:refines "atomic_size"} size() returns (x: int)
requires {:layer 1} Inv(queue, head, tail);
ensures {:layer 1} Inv(queue, head, tail);
{
  var c: Ref;

  yield;
  assert {:layer 1} Inv(queue, head, tail);

  x := 0;
  call c := Readhead();

  yield;
  assert {:layer 1} Inv(queue, head, tail);
  assert {:layer 1} (Used[c] && Btwn(next(queue), c, c, head))
    || Btwn(next(queue), head, c, null);

  while (c != null)
    invariant {:layer 1} Inv(queue, head, tail);
    invariant {:layer 1} (Used[c] && Btwn(next(queue), c, c, head))
      || Btwn(next(queue), head, c, null);
  {
    x := x + 1;
    call c := Load(c); // TODO: load doesn't return next if not in dom!?
    yield;
    assert {:layer 1} Inv(queue, head, tail);
    assert {:layer 1} (Used[c] && Btwn(next(queue), c, c, head))
                        || Btwn(next(queue), head, c, null); // AtomicTransferToqueue breaks this, but it shouldn't!?
  }
  yield;
  assert {:layer 1} Inv(queue, head, tail);
  return;
}
*/
