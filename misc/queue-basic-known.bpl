// ----------------------------------------
// A simple queue implementation
// based on the Michael-Scott queue.
// Assumes GC, so does not free dequeued nodes.
// Uses Grasshopper style heap encoding and axioms (using known terms as triggers).
// Also uses FP sets for linearity instead of Heaps and dom(heap).
//
// Use options -noinfer -typeEncoding:m -useArrayTheory
// ----------------------------------------

type Ref;
const null: Ref;

function {:builtin "MapConst"} MapConstBool(bool) : [Ref]bool;

const emptySet : [Ref]bool;
axiom (emptySet == MapConstBool(false));

// Linearity stuff:

function {:inline} {:linear "FP"} FPCollector(x: [Ref]bool) : [Ref]bool { x }


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
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {BtwnSet(f, x, z)[y]} BtwnSet(f, x, z)[y] <==> Btwn(f, x, y, z));
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {Btwn(f, x, y, z), BtwnSet(f, x, z)} Btwn(f, x, y, z) ==> BtwnSet(f, x, z)[y]);
axiom(forall f: [Ref]Ref, x: Ref, z: Ref :: {BtwnSet(f, x, z)} Btwn(f, x, x, x));
axiom(forall f: [Ref]Ref, x: Ref, z: Ref :: {BtwnSet(f, x, z)} Btwn(f, z, z, z));


//////////////////////////
// Axioms for Btwn
//////////////////////////

// read null
// axiom (forall f: [Ref]Ref :: f[null] == null);  // TODO UNSOUND!!! FIX!

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
var {:layer 0, 1} start: Ref; // The first head. To define UsedFP


// Abstract state
var {:layer 1,2} absArray: [int]Ref;  // TODO add keys (right now uses Ref)
var {:layer 1,2} absHead: int;
var {:layer 1,2} absTail: int;


function {:inline} Inv(queueFP: [Ref]bool, UsedFP: [Ref]bool, start: Ref,
    head: Ref, tail: Ref, next: [Ref]Ref,
    absArray: [int]Ref, absHead: int, absTail: int) : (bool)
{
  // There is a list from head to null
  Btwn(next, head, head, null)
    // TODO add triggers to these.
    && (forall x: Ref :: known(x) ==>
      (queueFP[x] <==> (Btwn(next, head, x, null) && x != null)))
    // Tail is on that list
    && Btwn(next, head, tail, null) && tail != null
    // There is also a list from start to head
    && Btwn(next, start, start, head)
    && (forall x: Ref :: known(x) ==>
      (UsedFP[x] <==> (Btwn(next, start, x, head) && x != head)))
    // Terms needed for axiom triggers
    && known(start) && known(head) && known(tail) && known(null) && knownF(next)
    // Properties of abstract state
    && 0 <= absHead && 0 <= absTail && absHead <= absTail
    && (forall i: int :: {absArray[i]}
      i < 0 || absTail < i <==> absArray[i] == null)
    // Relate abstract state to concrete state:
    && absArray[absHead] == head
    && (forall i: int :: {next[absArray[i]]} absArray[i + 1] == next[absArray[i]])
    && (forall y: Ref :: {Btwn(next, head, y, null), next[y]} known(y) ==>
      (Btwn(next, head, y, null) && next[y] == null ==> y == absArray[absTail]))
}


// ---------- Primitives for manipulating global state

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
    l_out := emptySet;
    queueFP := queueFP[newVal := true];
    assume knownF(next);
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
    queueFP := queueFP[oldVal := false];
    r := true;
  }
  else {
    r := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicTransferFromqueue"} TransferFromqueue(oldVal: Ref, newVal: Ref) returns (r: bool);


// ---------- Primitives for manipulating logical/abstract state

procedure {:layer 1} {:inline 1} intro_writeAbs(v: Ref)
  modifies absArray;
{
  absArray[absTail] := v;
}

procedure {:layer 1} {:inline 1} intro_incrHead()
  modifies absHead;
{
  absHead := absHead + 1;
}

procedure {:layer 1} {:inline 1} intro_incrTail()
  modifies absTail;
{
  absTail := absTail + 1;
}


// ---------- queue methods:

procedure {:atomic} {:layer 2} atomic_pop() returns (t: Ref)
  modifies absHead;
{
  t := absArray[absHead];
  absHead := absHead + 1;
}

procedure {:yields} {:layer 1} {:refines "atomic_pop"} pop() returns (h: Ref)
  requires {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
  ensures {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
{
  var g: bool;
  var t, x: Ref;

  yield;
  assert {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
  while (true)
    invariant {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
  {
    call h := Readhead();
    yield;
    assert {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
    assert {:layer 1} h == head || UsedFP[h];

    call t := Readtail();
    yield;
    assert {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
    assert {:layer 1} h == head || UsedFP[h];
    assert {:layer 1} (h == head && h != t ==> head != tail);

    if (h != t) {
      call x := Load(h);
      yield;
      assert {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
      assert {:layer 1} h == head || UsedFP[h];
      assert {:layer 1} (h == head && h != t ==> x == next[head]);
      assert {:layer 1} (h == head && h != t ==> head != tail);

      call g := TransferFromqueue(h, x);
      if (g) {
        // Linearization point. Update abstract state:
        call intro_incrHead();
        break;
      }
    }
    yield;
    assert {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
  }
  yield;
  assert {:expand} {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
}


procedure {:atomic} {:layer 2} atomic_push(x: Ref, {:linear_in "FP"} xFP: [Ref]bool)
  modifies absTail, absArray;
{
  absTail := absTail + 1;
  absArray[absTail] := x;
}

procedure {:yields} {:layer 1} {:refines "atomic_push"} push(x: Ref, {:linear_in "FP"} xFP: [Ref]bool)
  requires {:layer 1} xFP[x] && next[x] == null;
  requires {:layer 1} !Btwn(next, head, x, null);  // TODO get from linearity
  requires {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
  ensures {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
{
  var t, tn: Ref;
  var g: bool;
  var {:linear "FP"} tFP: [Ref]bool;

  yield;
  assert {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
  assert {:layer 1} !Btwn(next, head, x, null);
  assert {:layer 1} xFP[x] && next[x] == null;
  tFP := xFP;
  while (true)
    invariant {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
    invariant {:layer 1} known(x) && !Btwn(next, head, x, null);
    invariant {:layer 1} tFP == xFP && xFP[x] && next[x] == null;
  {
    call t := Readtail();
    yield;
    assert {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null;
    assert {:layer 1} t != null && (queueFP[t] || UsedFP[t]);
    assert {:layer 1} next[t] == null ==> queueFP[t];

    call tn := Load(t);
    yield;
    assert {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null;
    assert {:layer 1} t != null && (queueFP[t] || UsedFP[t]);
    assert {:layer 1} next[t] == null ==> queueFP[t];

    if (tn == null) {
      call g, tFP := TransferToqueue(t, tn, x, tFP);
      if (g) {
        // Linearization point. Update abstract state:
        call intro_incrTail();
        call intro_writeAbs(x);
        break;
      }
    } // TODO else cas tail
    yield;
    assert {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null;
  }
  yield;
  assert {:expand} {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
}


procedure {:atomic} {:layer 2} atomic_size() returns (x: int)
{}

procedure {:yields} {:layer 1} {:refines "atomic_size"} size() returns (x: int)
  requires {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
  ensures {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
{
  var c: Ref;

  yield;
  assert {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);

  x := 0;
  call c := Readhead();

  yield;
  assert {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
  assert {:layer 1} (UsedFP[c] || queueFP[c]);

  while (c != null)
    invariant {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
    invariant {:layer 1} known(c) && (UsedFP[c] || queueFP[c] || c == null);
  {
    x := x + 1;
    call c := Load(c);
    yield;
    assert {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
    assert {:layer 1} (UsedFP[c] || queueFP[c] || c == null);
  }
  yield;
  assert {:layer 1} Inv(queueFP, UsedFP, start, head, tail, next, absArray, absHead, absTail);
  return;
}
