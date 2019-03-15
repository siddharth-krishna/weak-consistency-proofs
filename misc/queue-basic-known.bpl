// ----------------------------------------
// A simple queue implementation
// based on the Michael-Scott queue.
// Assumes GC, so does not free dequeued nodes.
// Also uses the simplified heap encoding from CIVL's Treiber example.
// Also trying to use FP sets for linearity instead of Heaps and dom(heap).
//
// Use options -noinfer -typeEncoding:m -useArrayTheory
// ----------------------------------------

type Ref;
const null: Ref;

function {:builtin "MapConst"} MapConstBool(bool) : [Ref]bool;

function EmptyHeap(): ([Ref]bool);
axiom (EmptyHeap() == MapConstBool(false));

function Add(h: [Ref]bool, l: Ref): ([Ref]bool);
axiom (forall h: [Ref]bool, l: Ref :: Add(h, l) == h[l:=true]);

function Remove(h: [Ref]bool, l: Ref): ([Ref]bool);
axiom (forall h: [Ref]bool, l: Ref :: Remove(h, l) == h[l:=false]);

// Linearity stuff:

function {:inline} {:linear "FP"} NodeSetCollector(x: [Ref]bool) : [Ref]bool
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
axiom(forall S:[Ref]bool, T:[Ref]bool :: {Subset(S,T)} Subset(S,T) || (exists x:Ref :: known(x) && S[x] && !T[x]));


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
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {BtwnSet(f, x, z)[y]} BtwnSet(f, x, z)[y] <==> Btwn(f, x, y, z));
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {Btwn(f, x, y, z), BtwnSet(f, x, z)} Btwn(f, x, y, z) ==> BtwnSet(f, x, z)[y]);
axiom(forall f: [Ref]Ref, x: Ref, z: Ref :: {BtwnSet(f, x, z)} Btwn(f, x, x, x));
axiom(forall f: [Ref]Ref, x: Ref, z: Ref :: {BtwnSet(f, x, z)} Btwn(f, z, z, z));


//////////////////////////
// Axioms for Btwn
//////////////////////////

// read null
axiom (forall f: [Ref]Ref :: f[null] == null);

// reflexive
axiom(forall f: [Ref]Ref, x: Ref :: Btwn(f, x, x, x));

// step
axiom(forall f: [Ref]Ref, x: Ref :: {f[x]} Btwn(f, x, f[x], f[x]));

// reach
axiom(forall f: [Ref]Ref, x: Ref, y: Ref :: {f[x], known(y)} Btwn(f, x, y, y) ==> x == y || Btwn(f, x, f[x], y));

// cycle
axiom(forall f: [Ref]Ref, x: Ref, y:Ref :: {f[x], known(y)} f[x] == x && Btwn(f, x, y, y) ==> x == y);

// sandwich
axiom(forall f: [Ref]Ref, x: Ref, y: Ref :: {knownF(f), known(x), known(y), Btwn(f, x, y, x)} Btwn(f, x, y, x) ==> x == y);

// order1
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z), Btwn(f, x, y, y), Btwn(f, x, z, z)} Btwn(f, x, y, y) && Btwn(f, x, z, z) ==> Btwn(f, x, y, z) || Btwn(f, x, z, y));

// order2
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z), Btwn(f, x, y, z)} Btwn(f, x, y, z) ==> Btwn(f, x, y, y) && Btwn(f, y, z, z));

// transitive1
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z), Btwn(f, x, y, y), Btwn(f, y, z, z)} Btwn(f, x, y, y) && Btwn(f, y, z, z) ==> Btwn(f, x, z, z));

// transitive2
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, w: Ref :: {knownF(f), known(x), known(y), known(z), known(w), Btwn(f, x, y, z), Btwn(f, y, w, z)} Btwn(f, x, y, z) && Btwn(f, y, w, z) ==> Btwn(f, x, y, w) && Btwn(f, x, w, z));

// transitive3
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, w: Ref :: {knownF(f), known(x), known(y), known(z), known(w), Btwn(f, x, y, z), Btwn(f, x, w, y)} Btwn(f, x, y, z) && Btwn(f, x, w, y) ==> Btwn(f, x, w, z) && Btwn(f, w, y, z));

// relation between ReachW and Btwn
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z), ReachW(f, x, y, z)} ReachW(f, x, y, z) <==> (Btwn(f, x, y, z) || (Btwn(f, x, y, y) && !Btwn(f, x, z, z))));
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z), Btwn(f, x, y, z)} Btwn(f, x, y, z) <==> (ReachW(f, x, y, z) && ReachW(f, x, z, z)));

// btwn_write: grasshopper's update axiom
axiom (forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, u: Ref, v: Ref :: {f[u := v], known(x), known(y), known(z), Btwn(f[u := v], x, y, z)}
        u != null ==>
          (Btwn(f[u := v], x, y, z) <==>
          (Btwn(f, x, y, z) && ReachW(f, x, z, u))
          || (u != z && ReachW(f, x, u, z) && ReachW(f, v, z, u)
            && (Btwn(f, x, y, u) || Btwn(f, v, y, z)))));


// ---------- Shared state and invariant

// Fields:
var {:layer 0, 1} next: [Ref]Ref;

var {:linear "FP"} {:layer 0, 1} queueFP: [Ref]bool;
var {:linear "FP"} {:layer 0, 1} UsedFP: [Ref]bool;

var {:layer 0, 1} head: Ref;
var {:layer 0, 1} tail: Ref;


function {:inline} Inv(queueFP: [Ref]bool, UsedFP: [Ref]bool, head: Ref, tail: Ref, next: [Ref]Ref) : (bool)
{
  Btwn(next, head, head, null)
    && Btwn(next, head, tail, null)
    && Equal(BtwnSet(next, head, null),
             Union(Singleton(null), queueFP))
    && (forall x: Ref :: Btwn(next, x, x, head) ==> UsedFP[x])
    && tail != null
    && known(head) && known(tail) && known(null) && knownF(next)
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
  assert queueFP[i] || UsedFP[i];
  v := next[i];
  assume known(v);
}

procedure {:yields} {:layer 0} {:refines "AtomicLoad"} Load(i:Ref) returns (v:Ref);

procedure {:atomic} {:layer 1} AtomicStore({:linear "FP"} FP:[Ref]bool,
    i:Ref, v:Ref)
  modifies next;
{
  assert FP[i];
  next := next[i := v];
  assume knownF(next);
}

procedure {:yields} {:layer 0} {:refines "AtomicStore"}
  Store({:linear "FP"} FP:[Ref]bool, i:Ref, v:Ref);

procedure {:atomic} {:layer 1} AtomicTransferToqueue(t: Ref, oldVal: Ref,
    newVal: Ref, {:linear_in "FP"} l_in:[Ref]bool)
  returns (r: bool, {:linear "FP"} l_out:[Ref]bool)
  modifies next, queueFP;
{
  assert l_in[newVal];
  if (next[t] == oldVal) {
    next := next[t := newVal];
    l_out := EmptyHeap();
    queueFP := Add(queueFP, newVal);
    assume known(oldVal) && known(newVal) && known(next[newVal]) && knownF(next);
    r := true;
  } else {
    l_out := l_in;
    r := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicTransferToqueue"}
  TransferToqueue(t: Ref, oldVal: Ref, newVal: Ref,
                  {:linear_in "FP"} l_in:[Ref]bool)
  returns (r: bool, {:linear "FP"} l_out:[Ref]bool);

procedure {:atomic} {:layer 1} AtomicTransferFromqueue(oldVal: Ref, newVal: Ref) returns (r: bool)
  modifies head, UsedFP, queueFP;
{
  if (oldVal == head) {
    head := newVal;
    UsedFP[oldVal] := true;
    queueFP := Remove(queueFP, oldVal);
    assume known(oldVal) && known(head) && knownF(next);
    r := true;
  }
  else {
    r := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicTransferFromqueue"} TransferFromqueue(oldVal: Ref, newVal: Ref) returns (r: bool);


// ---------- queue methods:

procedure {:atomic} {:layer 2} atomic_pop() returns (t: Ref)
  modifies UsedFP, head, queueFP;
{
  // assume head != null;
  // t := head;
  // UsedFP[t] := true;
  // head := next[t];
  // queueFP := Remove(queueFP, t);
  // assume known(head) && knownF(next);
}

procedure {:yields} {:layer 1} {:refines "atomic_pop"} pop() returns (h: Ref)
requires {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
ensures {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
{
  var g: bool;
  var t, x: Ref;

  yield;
  assert {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
  while (true)
    invariant {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
  {
    call h := Readhead();
    yield;
    assert {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
    assert {:layer 1} h == head || UsedFP[h];

    call t := Readtail();
    yield;
    assert {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
    assert {:layer 1} h == head || UsedFP[h];
    assert {:layer 1} (h == head && h != t ==> head != tail);

    if (h != t) {
      call x := Load(h);
      yield;
      assert {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
      assert {:layer 1} h == head || UsedFP[h];
      assert {:layer 1} (h == head && h != t ==> x == next[head]);
      assert {:layer 1} (h == head && h != t ==> head != tail);

      call g := TransferFromqueue(h, x);
      if (g) {
        break;
      }
    }
    yield;
    assert {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
  }
  yield;
  assert {:expand} {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
}


procedure {:atomic} {:layer 2} atomic_push(x: Ref,
 {:linear_in "FP"} x_Heap: [Ref]bool)
 modifies queueFP, tail;
{
  // if (next[tail] == null) {
  //   queueFP := Add(queueFP, tail, x);
  //   queueFP := Add(queueFP, x, null);
  // }
  // tail := x;
}

procedure {:yields} {:layer 1} {:refines "atomic_push"} push(x: Ref, {:linear_in "FP"} x_Heap: [Ref]bool)
  requires {:layer 1} x_Heap[x] && next[x] == null && !Btwn(next, head, x, null);
  requires {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
  ensures {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
{
  var t, tn: Ref;
  var g: bool;
  var {:linear "FP"} t_Heap: [Ref]bool;

  yield;
  assert {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
  assert {:layer 1} !Btwn(next, head, x, null);
  assert {:layer 1} x_Heap[x] && next[x] == null;
  t_Heap := x_Heap;
  while (true)
    invariant {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
    invariant {:layer 1} !Btwn(next, head, x, null);
    invariant {:layer 1} t_Heap == x_Heap;
    invariant {:layer 1} x_Heap[x] && next[x] == null;
  {
    call t := Readtail();
    yield;
    assert {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} t_Heap == x_Heap;
    assert {:layer 1} x_Heap[x] && next[x] == null;
    assert {:layer 1} known(t) && t != null && (Btwn(next, head, t, null)
      || UsedFP[t]);
    assert {:layer 1} next[t] == null ==> t == tail;

    call tn := Load(t);
    yield;
    assert {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} t_Heap == x_Heap;
    assert {:layer 1} x_Heap[x] && next[x] == null;
    assert {:layer 1} known(t) && t != null && (Btwn(next, head, t, null)
      || UsedFP[t]);
    assert {:layer 1} next[t] == null ==> t == tail;

    if (tn == null) {
      call g, t_Heap := TransferToqueue(t, tn, x, t_Heap);
      if (g) {
        break;
      }
    } // TODO else cas tail
    yield;
    assert {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} t_Heap == x_Heap;
    assert {:layer 1} x_Heap[x] && next[x] == null;
  }
  yield;
  assert {:expand} {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
}


procedure {:atomic} {:layer 2} atomic_size() returns (x: int)
{}

procedure {:yields} {:layer 1} {:refines "atomic_size"} size() returns (x: int)
requires {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
ensures {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
{
  var c: Ref;
  var c1: Ref;

  yield;
  assert {:layer 1} Inv(queueFP, UsedFP, head, tail, next);

  x := 0;
  call c := Readhead();

  yield;
  assert {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
  assert {:layer 1} known(c) && ((UsedFP[c] && Btwn(next, c, c, head))
    || Btwn(next, head, c, null));

  while (c != null)
    invariant {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
    invariant {:layer 1} known(c) && ((UsedFP[c] && Btwn(next, c, c, head))
      || Btwn(next, head, c, null));
  {
    x := x + 1;
    call c1 := Load(c);
    yield;
    assert {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
    assert {:layer 1} known(c) && ((UsedFP[c] && Btwn(next, c, c, head))
                        || Btwn(next, head, c, null));
  }
  yield;
  assert {:layer 1} Inv(queueFP, UsedFP, head, tail, next);
  return;
}
