// ----------------------------------------
// A simple queue implementation
// based on the Michael-Scott queue.
// Assumes GC, so does not free dequeued nodes.
// Uses Grasshopper style heap encoding and axioms (using known terms as triggers).
// Also uses FP sets for linearity instead of Heaps and dom(heap).
//
// Proof does not go through because in the case that pop returns EMPTY the
// linearization point is future-dependant and I don't think CIVL can prove this!
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
var {:layer 1,2} absArray: [int]Key;
var {:layer 1,2} absHead: int;
var {:layer 1,2} absTail: int;
var {:layer 1,2} absRefs: [int]Ref;  // connection between abstract and concrete


function {:inline} Inv(queueFP: [Ref]bool, usedFP: [Ref]bool, start: Ref,
    head: Ref, tail: Ref, next: [Ref]Ref, data: [Ref]Key,
    absArray: [int]Key, absRefs: [int]Ref, absHead: int, absTail: int) : (bool)
{
  // There is a list from head to null
  Btwn(next, head, head, null)
  && (forall x: Ref :: {queueFP[x]}{Btwn(next, head, x, null)}
    known(x) ==> (queueFP[x] <==> (Btwn(next, head, x, null) && x != null)))
  // Tail is on that list
  && Btwn(next, head, tail, null) && tail != null
  // There is also a list from start to head // TODO try just lseg(c, head)
  && Btwn(next, start, start, head)
  && (forall x: Ref :: {usedFP[x]}{Btwn(next, start, x, head)}
    known(x) ==> (usedFP[x] <==> (Btwn(next, start, x, head) && x != head)))
  // Terms needed for axiom triggers
  && known(start) && known(head) && known(tail) && known(null) && knownF(next)
  // Properties of abstract state
  && 0 <= absHead && 0 <= absTail && absHead <= absTail
  // Relate abstract state to concrete state:
  && (forall i: int :: {absRefs[i]}
    i < -1 || absTail <= i <==> absRefs[i] == null)
  && absRefs[absHead - 1] == head
  && (forall i: int :: {next[absRefs[i]]} 
    -1 <= i && i < absTail ==> absRefs[i + 1] == next[absRefs[i]])
  && (forall i: int :: {absArray[i], data[absRefs[i]]}
    0 <= i && i < absTail ==> absArray[i] == data[absRefs[i]])
  && (forall y: Ref :: {Btwn(next, head, y, null), next[y]} known(y) ==>
    (Btwn(next, head, y, null) && next[y] == null ==> y == absRefs[absTail - 1]))
}

  // assert {:layer 1} Btwn(next, head, head, null);
  // assert {:layer 1} (forall x1: Ref :: {queueFP[x1]}{Btwn(next, head, x1, null)}
  //   known(x) ==> (queueFP[x] <==> (Btwn(next, head, x, null) && x != null)));
  // // Tail is on that list
  // assert {:layer 1} Btwn(next, head, tail, null) && tail != null;
  // // If head != tail, there's at least 2 nodes in the list
  // assert {:layer 1} (head != tail ==> queueFP[next[head]]);
  // // There is also a list from start to head // TODO try just lseg(c, head)
  // assert {:layer 1} Btwn(next, start, start, head);
  // assert {:layer 1} (forall x1: Ref :: {usedFP[x1]}{Btwn(next, start, x1, head)}
  //   known(x) ==> (usedFP[x] <==> (Btwn(next, start, x, head) && x != head)));
  // // Properties of abstract state
  // assert {:layer 1} 0 <= absHead && 0 <= absTail && absHead <= absTail;
  // // Relate abstract state to concrete state:
  // assert {:layer 1} (forall i: int :: {absRefs[i]}
  //   i < -1 || absTail <= i <==> absRefs[i] == null);
  // assert {:layer 1} absRefs[absHead - 1] == head;
  // assert {:layer 1} (forall i: int :: {next[absRefs[i]]} 
  //   -1 <= i && i < absTail ==> absRefs[i + 1] == next[absRefs[i]]);
  // assert {:layer 1} (forall i: int :: {absArray[i], data[absRefs[i]]}
  //   0 <= i && i < absTail ==> absArray[i] == data[absRefs[i]]);
  // assert {:layer 1} (forall y: Ref :: {Btwn(next, head, y, null), next[y]} known(y) ==>
  //   (Btwn(next, head, y, null) && next[y] == null ==> y == absRefs[absTail - 1]));

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
  assume known(y);
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
  assume knownF(next);
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
    assume knownF(next);
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

procedure {:layer 1} {:inline 1} intro_writeAbs(k: Key, x: Ref)
  modifies absArray, absRefs;
{
  absArray[absTail] := k;
  absRefs[absTail] := x;
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

procedure {:atomic} {:layer 2} atomic_pop() returns (k: Key)
  modifies absHead;
{
  if (absHead != absTail) {
    k := absArray[absHead];
    absHead := absHead + 1;
  }
}

procedure {:yields} {:layer 1} {:refines "atomic_pop"} pop() returns (k: Key)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
{
  var b: bool;
  var h, t, hn: Ref;

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
  while (true)
    invariant {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
  {
    call h := readHead();
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
    assert {:layer 1} h == head || usedFP[h];
    assert {:layer 1} (h == tail && next[h] == null) || queueFP[next[h]] || usedFP[next[h]];
    assert {:layer 1} h == tail && next[h] == null ==> absHead == absTail;

    call t := readTail();
    // This is the LP in the Empty case, but we don't know this until later!
    // TODO try checking if h == t && next[h] == null in ghost code and forcing LP to happen here?
    assert {:layer 1} h == t && next[h] == null ==> absHead == absTail;
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
    assert {:layer 1} h == head || usedFP[h];
    assert {:layer 1} (h == t && next[h] == null) || queueFP[next[h]] || usedFP[next[h]];
    assert {:layer 1} (h == head && h != t ==> head != tail);
    assert {:layer 1} h == t && t == tail ==> Btwn(next, head, next[h], null);

    call hn := readNext(h);
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
    assert {:layer 1} h == head || usedFP[h];
    assert {:layer 1} (h == t && hn == null) || queueFP[hn] || usedFP[hn];
    assert {:layer 1} (h == head && h != t ==> head != tail && hn == next[head]);
    // assert {:layer 1} h == t && hn == null ==> absHead == absTail;
    assert {:layer 1} h == t && t == tail ==> Btwn(next, head, hn, null);

    if (h == t) {
      if (hn == null) {
        // assert {:layer 1} absHead == absTail;
        // k := EMPTY; // TODO
        break;
      } else {
        call b := casTail(t, hn);
      }
    } else {
      call k := readData(hn);
      yield;
      assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
      assert {:layer 1} h == head || usedFP[h];
      assert {:layer 1} (h == head && h != t ==> head != tail && hn == next[head]);
      assert {:layer 1} data[hn] == k;

      call b := casHeadTransfer(h, hn);
      if (b) {
        assert {:layer 1} absHead != absTail && k == absArray[absHead];
        // Linearization point. Update abstract state:
        call intro_incrHead();
        break;
      }
    }
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
  }
  yield;
  assert {:expand} {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
}


procedure {:atomic} {:layer 2} atomic_push(k: Key, x: Ref, {:linear_in "FP"} xFP: [Ref]bool)
  modifies absArray, absTail, absRefs;
{
  absRefs[absTail] := x;
  absArray[absTail] := k;
  absTail := absTail + 1;
}

procedure {:yields} {:layer 1} {:refines "atomic_push"} push(k: Key, x: Ref,
    {:linear_in "FP"} xFP: [Ref]bool)
  requires {:layer 1} xFP[x] && next[x] == null && data[x] == k;  // TODO alloc x with k
  requires {:layer 1} !Btwn(next, head, x, null);  // TODO get from linearity
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
{
  var t, tn: Ref;
  var b: bool;
  var {:linear "FP"} tFP: [Ref]bool;

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
  assert {:layer 1} !Btwn(next, head, x, null);
  assert {:layer 1} xFP[x] && next[x] == null && data[x] == k;
  tFP := xFP;
  while (true)
    invariant {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
    invariant {:layer 1} known(x) && !Btwn(next, head, x, null);
    invariant {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k;
  {
    call t := readTail();
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k;
    assert {:layer 1} t != null && (queueFP[t] || usedFP[t]);
    assert {:layer 1} next[t] == null ==> queueFP[t];

    call tn := readNext(t);
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k;
    assert {:layer 1} t != null && (queueFP[t] || usedFP[t]);
    assert {:layer 1} next[t] == null ==> queueFP[t];
    assert {:layer 1} tn != null ==> tn == next[t];

    if (tn == null) {
      call b, tFP := casNextTransfer(t, tn, x, tFP);
      if (b) {
        // Linearization point. Update abstract state:
        call intro_writeAbs(k, x);
        call intro_incrTail();
        break;
      }
    } else {
      call b := casTail(t, tn);
    }
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k;
  }
  yield;
  assert {:expand} {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
}

/*

procedure {:atomic} {:layer 2} atomic_size() returns (s: int)
{}

// Size invariant: s == indexOf[c] - old(absHead)
procedure {:yields} {:layer 1} {:refines "atomic_size"} size() returns (s: int)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
{
  var c: Ref;

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);

  s := 0;
  call c := readHead();

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
  assert {:layer 1} (usedFP[c] || queueFP[c]);

  while (c != null)
    invariant {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
    invariant {:layer 1} known(c) && (usedFP[c] || queueFP[c] || c == null);
  {
    s := s + 1;
    call c := readNext(c);
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
    assert {:layer 1} (usedFP[c] || queueFP[c] || c == null);
  }
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, absArray, absRefs, absHead, absTail);
  return;
}

*/