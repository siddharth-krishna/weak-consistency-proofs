// ----------------------------------------
// A simple queue implementation based on the Michael-Scott queue.
// Assumes GC, so does not free dequeued nodes.
//
// Compared to Java's ConcurrentLinkedQueue, we:
// - Do not link nodes to themselves when popping
// - Do not set items to null when removing/popping
// - Do not allow head to lag behind
//
// Use options -noinfer -typeEncoding:m -useArrayTheory
// ----------------------------------------


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

// Tags storing write operations:
var {:layer 0, 1} nextTags: [Ref]SetInvoc;
var {:layer 0, 1} dataTags: [Ref]SetInvoc;
var {:layer 0, 1} headTags: SetInvoc;
var {:layer 0, 1} tailTags: SetInvoc;

// Witness to prove that nextTags contains singleton sets
var {:layer 1, 1} nextInvoc: [Ref]Invoc;
// Witness for node that contains invoc in nextTags
var {:layer 1, 1} nextRef: [Invoc]Ref;

// Layer 1 witness mapping linearized and not-yet-returned ops to return value
var {:layer 1,1} retK: [Invoc]Key;
var {:layer 1,1} retS: [Invoc]int;

// The set of invocations that have been called
var {:layer 1,1} called: [Invoc]bool;

// The set of invocations that have returned
var {:layer 1,1} returned: [Invoc]bool;


// Abstract state
var {:layer 1,1} absRefs: [int]Ref;  // connection between abstract and concrete


function {:inline} Inv(queueFP: [Ref]bool, usedFP: [Ref]bool, start: Ref,
    head: Ref, tail: Ref, next: [Ref]Ref, data: [Ref]Key,
    nextTags: [Ref]SetInvoc, nextInvoc: [Ref]Invoc, nextRef: [Invoc]Ref,
    lin: SeqInvoc, vis: [Invoc]SetInvoc, absRefs: [int]Ref,
    called: [Invoc]bool, returned: [Invoc]bool) : bool
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
  // Relate abstract state to concrete state:
  && (forall i: int :: {absRefs[i]}
    i < -1 || Queue.stateTail(Queue.ofSeq(lin)) <= i <==> absRefs[i] == null)
  && absRefs[Queue.stateHead(Queue.ofSeq(lin)) - 1] == head
  && (forall i: int :: {next[absRefs[i]]}
    -1 <= i && i < Queue.stateTail(Queue.ofSeq(lin))
    ==> absRefs[i + 1] == next[absRefs[i]])
  && (forall i, j: int :: {absRefs[i], absRefs[j]}
    absRefs[i] == absRefs[j] && absRefs[i] != null ==> i == j)
  && (forall i: int :: {Queue.stateArray(Queue.ofSeq(lin))[i], data[absRefs[i]]}
    0 <= i && i < Queue.stateTail(Queue.ofSeq(lin))
    ==> Queue.stateArray(Queue.ofSeq(lin))[i] == data[absRefs[i]])
  && (forall y: Ref :: {Btwn(next, head, y, null), next[y]} known(y) ==>
    (Btwn(next, head, y, null) && y != null && next[y] == null
    ==> y == absRefs[Queue.stateTail(Queue.ofSeq(lin)) - 1]))
  // nextTags only contains singleton sets of push operations
  && (forall y: Ref :: {known(y)} known(y) ==>  // TODO trigger?
    (Btwn(next, start, y, null) && y != null && next[y] != null
    ==> nextTags[y] == Set(nextInvoc[y]) && invoc_m(nextInvoc[y]) == Queue.push))
  && nextTags[absRefs[Queue.stateTail(Queue.ofSeq(lin)) - 1]] == Set_empty
  // lin is made up of nextInvoc[y] for y in the queue
  && (forall n: Invoc :: {Seq_elem(n, lin)} known(nextRef[n]) && invoc_m(n) == Queue.push ==>
    (Seq_elem(n, lin) 
      <==> Btwn(next, start, nextRef[n], null)
        && nextRef[n] != null && next[nextRef[n]] != null))
  // lin is ordered by order of nodes in queue
  && (forall n1, n2: Invoc :: {Seq_ord(lin, n1, n2)}
    known(nextRef[n1]) && known(nextRef[n2]) ==>
    (invoc_m(n1) == Queue.push && invoc_m(n2) == Queue.push
    && Seq_elem(n1, lin) && Seq_elem(n2, lin)
    ==> (Seq_ord(lin, n1, n2)
      <==> Btwn(next, nextRef[n1], nextRef[n1], nextRef[n2]) && nextRef[n1] != nextRef[n2])))
  // Default value for nextRef is null
  && (forall n: Invoc :: {nextRef[n]}
    !Seq_elem(n, lin) || invoc_m(n) != Queue.push ==> nextRef[n] == null)
  // nextRef is injective (for pushes in lin)
  && (forall n1, n2: Invoc :: {nextRef[n1], nextRef[n2]}
    Seq_elem(n1, lin) && Seq_elem(n2, lin)
    && invoc_m(n1) == Queue.push && invoc_m(n2) == Queue.push
    && nextRef[n1] == nextRef[n2] ==> n1 == n2)
  // nextRef and nextInvoc are inverses
  // && (forall n: Invoc :: {nextInvoc[nextRef[n]]} nextInvoc[nextRef[n]] == n)
  && (forall y: Ref :: {nextRef[nextInvoc[y]]} known(y) ==>
    (Btwn(next, start, y, null) && next[y] != null ==> nextRef[nextInvoc[y]] == y))
  // lin only contains called things
  && (forall n: Invoc :: {Seq_elem(n, lin)} Seq_elem(n, lin) ==> called[n])
  // lin contains distinct elements
  && Seq_distinct(lin)
  // vis sets only contain linearized ops
  && (forall n1, n2: Invoc :: {Set_elem(n1, vis[n2])}
    Set_elem(n1, vis[n2]) && returned[n2] ==> Set_elem(n1, Set_ofSeq(lin)))
  // Used to infer that invocations don't modify vis after they've returned
  && (forall n1, n2 : Invoc :: called[n1] && hb(n2, n1) ==> returned[n2])
  // To establish precondition of intro_writeLin
  && (forall n: Invoc :: returned[n] ==> Seq_elem(n, lin))
  // Axiom of heap encoding
  && next[null] == null
}

function {:inline} preLP(called: [Invoc]bool, returned: [Invoc]bool, lin: SeqInvoc, this: Invoc) : bool
{
  called[this] && !returned[this] && !Seq_elem(this, lin)
}

function {:inline} postLP(called: [Invoc]bool, returned: [Invoc]bool, lin: SeqInvoc, this: Invoc) : bool
{
  called[this] && !returned[this] && Seq_elem(this, lin)
}


// ---------- Primitives for manipulating global state

procedure {:atomic} {:layer 1} readHead_atomic() returns (x: Ref)
{ x := head; }

procedure {:yields} {:layer 0} {:refines "readHead_atomic"} readHead() returns (x: Ref);

procedure {:atomic} {:layer 1} readTail_atomic() returns (x: Ref)
{ x := tail; }

procedure {:yields} {:layer 0} {:refines "readTail_atomic"} readTail() returns (x: Ref);

procedure {:atomic} {:layer 1} casTail_atomic(ole: Ref, new: Ref, {:linear "this"} n: Invoc)
  returns (b: bool)
  modifies tail, tailTags;
{
  if (tail == ole) {
    tail := new;
    tailTags := Set_add(tailTags, n);
    b := true;
  } else {
    b := false;
  }
}

procedure {:yields} {:layer 0} {:refines "casTail_atomic"}
  casTail(ole: Ref, new: Ref, {:linear "this"} n: Invoc) returns (b: bool);

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

procedure {:atomic} {:layer 1} writeNext_atomic(x: Ref, y: Ref,
    {:linear "FP"} FP:[Ref]bool, {:linear "this"} n: Invoc)
  modifies next, nextTags;
{
  assert FP[x];
  next := next[x := y];
  nextTags[x] := Set_add(nextTags[x], n);
  assume knownF(next);
}

procedure {:yields} {:layer 0} {:refines "writeNext_atomic"}
  writeNext(x: Ref, y: Ref, {:linear "FP"} FP:[Ref]bool, {:linear "this"} n: Invoc);

procedure {:atomic} {:layer 1} casNextTransfer_atomic(x: Ref, oldVal: Ref,
    newVal: Ref, {:linear_in "FP"} inFP:[Ref]bool, {:linear "this"} n: Invoc)
  returns (b: bool, {:linear "FP"} outFP:[Ref]bool)
  modifies next, queueFP, nextTags;
{
  assert inFP[newVal];
  if (next[x] == oldVal) {
    next := next[x := newVal];
    nextTags[x] := Set_add(nextTags[x], n);
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
  casNextTransfer(x: Ref, oldVal: Ref, newVal: Ref, {:linear_in "FP"} inFP:[Ref]bool,
    {:linear "this"} n: Invoc)
  returns (b: bool, {:linear "FP"} outFP:[Ref]bool);

procedure {:atomic} {:layer 1} casHeadTransfer_atomic(oldVal: Ref, newVal: Ref,
    {:linear "this"} n: Invoc)
  returns (b: bool)
  modifies head, usedFP, queueFP, headTags;
{
  if (oldVal == head) {
    head := newVal;
    headTags := Set_add(headTags, n);
    usedFP[oldVal] := true;
    queueFP := queueFP[oldVal := false];
    b := true;
  }
  else {
    b := false;
  }
}

procedure {:yields} {:layer 0} {:refines "casHeadTransfer_atomic"}
  casHeadTransfer(oldVal: Ref, newVal: Ref, {:linear "this"} n: Invoc) returns (b: bool);


// ---------- Primitives for manipulating logical/abstract state

procedure {:layer 1} {:inline 1} intro_writeAbsRefs(k: Key, x: Ref)
  modifies absRefs;
{
  absRefs[Queue.stateTail(Queue.ofSeq(lin))] := x;
}

procedure {:layer 1} {:inline 1} intro_getHeadIndex() returns (ci: int)
{
  ci := Queue.stateHead(Queue.ofSeq(lin));
}

// Return the tail of the concrete queue
procedure {:layer 1} {:inline 1} intro_getTail() returns (t: Ref);
  ensures {:layer 1} known(t) && t != null && next[t] == null && Btwn(next, head, t, null);

// Return the tail of the abstract queue
procedure {:layer 1} {:inline 1} intro_getTailIndex() returns (ti: int)
{
  ti := Queue.stateTail(Queue.ofSeq(lin));
}


procedure {:layer 1} {:inline 1} intro_writeNextInvoc(x: Ref, n: Invoc)
  modifies nextInvoc, nextRef;
{
  nextInvoc[x] := n;
  nextRef[n] := x;
}

procedure {:layer 1} intro_readNextTags(x: Ref, v: SetInvoc) returns (v1: SetInvoc)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  requires {:layer 1} known(x) && Btwn(next, start, x, null) && x != null;
  ensures {:layer 1} next[x] == null ==> v1 == v;
  ensures {:layer 1} next[x] != null ==> Seq_elem(nextInvoc[x], lin) && v1 == Set_add(v, nextInvoc[x]);
{
  v1 := Set_union(v, Set_inter(nextTags[x], Set_ofSeq(lin)));
  // Trigger some axioms:
  assert {:layer 1} (forall n: Invoc :: {Set_elem(n, v1)} Set_elem(n, v1)
    <==> Set_elem(n, v) || (Set_elem(n, nextTags[x]) && Set_elem(n, Set_ofSeq(lin))));
  assert {:layer 1} next[x] != null ==> Set_equal(v1, Set_add(v, nextInvoc[x]));
}

procedure {:layer 1} {:inline 1} intro_writeCalled({:linear "this"} this: Invoc)
  modifies called;
{
  called[this] := true;
}

procedure {:layer 1} {:inline 1} intro_writeReturned({:linear "this"} this: Invoc)
  modifies returned;
{
  returned[this] := true;
}


// ---------- Implementation of Queue:


procedure {:yields} {:layer 1} {:refines "pop_call_atomic"}
    pop_call({:linear "this"} this: Invoc)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  // everything before this has returned
  requires {:layer 1} (forall n1: Invoc :: hb(n1, this) ==> returned[n1]);
  // this has not been called or returned yet
  requires {:layer 1} (!called[this] && !returned[this]);
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  ensures {:layer 1} preLP(called, returned, lin, this);
  modifies called;
{
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  assert {:layer 1} (forall n1: Invoc :: hb(n1, this) ==> returned[n1]);
  assert {:layer 1} (!called[this] && !returned[this]);

  call intro_writeCalled(this);
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  assert {:layer 1} preLP(called, returned, lin, this);
}

procedure {:yields} {:layer 1} {:refines "pop_atomic"} pop({:linear "this"} this: Invoc)
  returns (k: Key)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  requires {:layer 1} invoc_m(this) == Queue.pop;
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && postLP(called, returned, lin, this);
  ensures {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
{
  var {:layer 1} my_vis: SetInvoc;
  var b: bool;
  var h, t, hn: Ref;

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  while (true)
    invariant {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  {
    call h := readHead();
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} h == head || usedFP[h];

    call t := readTail();
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} h == head || usedFP[h];
    assert {:layer 1} (h == head && h != t ==> head != tail);

    call hn := readNext(h);
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} h == head || usedFP[h];
    assert {:layer 1} (h == t && hn == null) || queueFP[hn] || usedFP[hn];
    assert {:layer 1} (h == head && h != t ==> head != tail && hn == next[head]);

    if (h != t) {
      call k := readData(hn);
      yield;
      assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
      assert {:layer 1} h == head || usedFP[h];
      assert {:layer 1} (h == head && h != t ==> head != tail && hn == next[head]);
      assert {:layer 1} data[hn] == k;

      call b := casHeadTransfer(h, hn, this);
      if (b) {
        // Linearization point.
        call my_vis := intro_readLin();
        call intro_writeLin(this);
        call intro_writeVis(this, my_vis);

        break;
      }
    }
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  }
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
}

procedure {:yields} {:layer 1} {:refines "pop_return_atomic"}
    pop_return({:linear "this"} this: Invoc)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  requires {:layer 1} postLP(called, returned, lin, this);
  requires {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  modifies returned;
{
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  assert {:layer 1} postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));

  call intro_writeReturned(this);

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
}


procedure {:yields} {:layer 1} {:refines "push_call_atomic"}
    push_call({:linear "this"} this: Invoc)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  // everything before this has returned
  requires {:layer 1} (forall n1: Invoc :: hb(n1, this) ==> returned[n1]);
  // this has not been called or returned yet
  requires {:layer 1} (!called[this] && !returned[this]);
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  ensures {:layer 1} preLP(called, returned, lin, this);
  modifies called;
{
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  assert {:layer 1} (forall n1: Invoc :: hb(n1, this) ==> returned[n1]);
  assert {:layer 1} (!called[this] && !returned[this]);

  call intro_writeCalled(this);
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  assert {:layer 1} preLP(called, returned, lin, this);
}

procedure {:yields} {:layer 1} {:refines "push_atomic"} push(k: Key, x: Ref,
    {:linear_in "FP"} xFP: [Ref]bool, {:linear "this"} this: Invoc)
  requires {:layer 1} xFP[x] && next[x] == null && data[x] == k && nextTags[x] == Set_empty;  // TODO alloc x with k
  requires {:layer 1} !Btwn(next, head, x, null);  // TODO get from linearity
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  requires {:layer 1} invoc_m(this) == Queue.push && invoc_k(this) == k;
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && postLP(called, returned, lin, this);
{
  var {:layer 1} my_vis: SetInvoc;
  var t, tn: Ref;
  var b: bool;
  var {:linear "FP"} tFP: [Ref]bool;

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  assert {:layer 1} !Btwn(next, head, x, null);
  assert {:layer 1} xFP[x] && next[x] == null && data[x] == k && nextTags[x] == Set_empty;
  tFP := xFP;
  while (true)
    invariant {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    invariant {:layer 1} known(x) && !Btwn(next, head, x, null);
    invariant {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k && nextTags[x] == Set_empty;
  {
    call t := readTail();
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k && nextTags[x] == Set_empty;
    assert {:layer 1} t != null && (queueFP[t] || usedFP[t]);
    assert {:layer 1} next[t] == null ==> queueFP[t];

    call tn := readNext(t);
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k && nextTags[x] == Set_empty;
    assert {:layer 1} t != null && (queueFP[t] || usedFP[t]);
    assert {:layer 1} next[t] == null ==> queueFP[t];
    assert {:layer 1} tn != null ==> tn == next[t];

    if (tn == null) {
      call b, tFP := casNextTransfer(t, tn, x, tFP, this);
      if (b) {
        // Linearization point.
        call intro_writeNextInvoc(t, this);
        call intro_writeAbsRefs(k, x);
        call my_vis := intro_readLin();
        call intro_writeLin(this);
        call intro_writeVis(this, my_vis);

        break;
      }
    } else {
      call b := casTail(t, tn, this);
    }
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k && nextTags[x] == Set_empty;
  }
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
}

procedure {:yields} {:layer 1} {:refines "push_return_atomic"}
    push_return({:linear "this"} this: Invoc)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  requires {:layer 1} postLP(called, returned, lin, this);
  requires {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  modifies returned;
{
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  assert {:layer 1} postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));

  call intro_writeReturned(this);

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
}


procedure {:yields} {:layer 1} {:refines "size_call_atomic"}
    size_call({:linear "this"} this: Invoc)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  // everything before this has returned
  requires {:layer 1} (forall n1: Invoc :: hb(n1, this) ==> returned[n1]);
  // this has not been called or returned yet
  requires {:layer 1} (!called[this] && !returned[this]);
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  ensures {:layer 1} preLP(called, returned, lin, this);
  modifies called;
{
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  assert {:layer 1} (forall n1: Invoc :: hb(n1, this) ==> returned[n1]);
  assert {:layer 1} (!called[this] && !returned[this]);

  call intro_writeCalled(this);
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  assert {:layer 1} preLP(called, returned, lin, this);
}

procedure {:yields} {:layer 1} {:refines "size_atomic"} size({:linear "this"} this: Invoc) returns (s: int)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  requires {:layer 1} invoc_m(this) == Queue.size;
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && postLP(called, returned, lin, this);
{
  var {:layer 1} my_vis: SetInvoc;
  var {:layer 1} t0i: int; var {:layer 1} ci: int;
  var {:layer 1} t0: Ref;
  var c, cn: Ref;
  var {:layer 1} old_vis: SetInvoc;
  var {:layer 1} old_c: Ref;

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);

  s := 0;
  call c := readHead();
  call ci := intro_getHeadIndex();
  call t0 := intro_getTail();
  call t0i := intro_getTailIndex();
  call my_vis := intro_readLin();

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  assert {:layer 1} (forall j: Invoc :: hb(j, this) ==> Set_subset(vis[j], my_vis));
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, my_vis)}
    Set_elem(n1, my_vis) ==> Set_elem(n1, Set_ofSeq(lin)));
  assert {:layer 1} (usedFP[c] || queueFP[c]);
  assert {:layer 1} ci == Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis)));
  assert {:layer 1} t0i == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)));
  assert {:layer 1} known(t0) && t0 != null && Btwn(next, start, t0, null);
  assert {:layer 1} known(c) && Btwn(next, start, c, t0);
  assert {:layer 1} c == absRefs[ci - 1] && t0 == absRefs[t0i - 1];
  assert {:layer 1} (forall n: Invoc :: {Set_elem(n, my_vis)}
    known(nextRef[n]) && invoc_m(n) == Queue.push ==>
    (Set_elem(n, my_vis) <==> Btwn(next, start, nextRef[n], t0) && nextRef[n] != t0));
  assert {:layer 1} (forall n1, n2: Invoc :: {Seq_ord(lin, n1, n2)} known(nextRef[n2]) ==>
    (Seq_elem(n1, Seq_restr(lin, my_vis)) && Seq_elem(n2, lin) && !Set_elem(n2, my_vis)
    && invoc_m(n2) == Queue.push ==> Seq_ord(lin, n1, n2)));

  call cn := readNext(c);
  old_vis := my_vis;
  call my_vis := intro_readNextTags(c, my_vis);
  if (cn != null) {
    ci := ci + 1;
  }

  // Case 1
  assert {:layer 1} Btwn(next, start, c, t0) && c != t0
    ==> Set_elem(nextInvoc[c], old_vis);
  assert {:layer 1} Btwn(next, start, c, t0) && c != t0
    ==> old_vis == my_vis
    && t0i == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
    && ((cn == null && c == absRefs[ci - 1]) || (cn != null && c == absRefs[ci - 2]))
    && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis)));
  // Case 2  -- restr(lin, my_vis) == append(restr(lin, old_vis), nextInvoc[c])
  assert {:layer 1} Btwn(next, t0, c, null) && next[c] != null
    ==> Seq_restr(lin, my_vis) == Seq_append(Seq_restr(lin, old_vis), nextInvoc[c]);
  assert {:layer 1} Btwn(next, t0, c, null) && next[c] != null
    ==> ci == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
      && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis)));

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  assert {:layer 1} (forall j: Invoc :: hb(j, this) ==> Set_subset(vis[j], my_vis));
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, my_vis)}
    Set_elem(n1, my_vis) ==> Set_elem(n1, Set_ofSeq(lin)));
  assert {:layer 1} (usedFP[c] || queueFP[c]) && known(c) && (cn != null ==> cn == next[c]);
  assert {:layer 1} cn == null ==> Btwn(next, t0, c, null);
  assert {:layer 1} ((cn == null && c == absRefs[ci - 1]) || (cn != null && c == absRefs[ci - 2])) && t0 == absRefs[t0i - 1];
  assert {:layer 1} known(t0) && t0 != null && Btwn(next, start, t0, null);
  assert {:layer 1} (Btwn(next, start, c, t0) && c != t0
      && t0i == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
      && (forall n: Invoc :: {Set_elem(n, my_vis)}
        known(nextRef[n]) && invoc_m(n) == Queue.push ==>
        (Set_elem(n, my_vis) <==> Btwn(next, start, nextRef[n], t0) && nextRef[n] != t0))
      && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))
    || (Btwn(next, t0, c, null)
      && ci == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
      && (forall n: Invoc :: {Set_elem(n, my_vis)}
        known(nextRef[n]) && invoc_m(n) == Queue.push ==>
        (Set_elem(n, my_vis) <==> Btwn(next, start, nextRef[n], c) && (cn != null || nextRef[n] != c)))
      && ((cn == null && s == ci - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))
        || (cn != null && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))));
  assert {:layer 1} (forall n1, n2: Invoc :: {Seq_ord(lin, n1, n2)} known(nextRef[n2]) ==>
    (Seq_elem(n1, Seq_restr(lin, my_vis)) && Seq_elem(n2, lin) && !Set_elem(n2, my_vis)
    && invoc_m(n2) == Queue.push ==> Seq_ord(lin, n1, n2)));

  while (cn != null)
    invariant {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    invariant {:layer 1} (forall j: Invoc ::
      hb(j, this) ==> Set_subset(vis[j], my_vis));
    invariant {:layer 1} (forall n1: Invoc :: {Set_elem(n1, my_vis)}
      Set_elem(n1, my_vis) ==> Set_elem(n1, Set_ofSeq(lin)));
    invariant {:layer 1} known(c) && (usedFP[c] || queueFP[c]);
    invariant {:layer 1} known(cn) && (cn != null ==> next[c] == cn);
    invariant {:layer 1} cn == null ==> Btwn(next, t0, c, null);
    invariant {:layer 1} known(t0) && t0 != null && Btwn(next, start, t0, null);
    invariant {:layer 1} ((cn == null && c == absRefs[ci - 1]) || (cn != null && c == absRefs[ci - 2])) && t0 == absRefs[t0i - 1];
    invariant {:layer 1} (Btwn(next, start, c, t0) && c != t0
        && t0i == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
        && (forall n: Invoc :: {Set_elem(n, my_vis)}
          known(nextRef[n]) && invoc_m(n) == Queue.push ==>
          (Set_elem(n, my_vis) <==> Btwn(next, start, nextRef[n], t0) && nextRef[n] != t0))
        && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))
      || (Btwn(next, t0, c, null)
        && ci == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
        && (forall n: Invoc :: {Set_elem(n, my_vis)}
          known(nextRef[n]) && invoc_m(n) == Queue.push ==>
          (Set_elem(n, my_vis) <==> Btwn(next, start, nextRef[n], c)
            && (cn != null || nextRef[n] != c)))
        && ((cn == null && s == ci - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))
          || (cn != null && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))));
    invariant {:layer 1} (forall n1, n2: Invoc :: {Seq_ord(lin, n1, n2)} known(nextRef[n2]) ==>
      (Seq_elem(n1, Seq_restr(lin, my_vis)) && Seq_elem(n2, lin) && !Set_elem(n2, my_vis)
      && invoc_m(n2) == Queue.push ==> Seq_ord(lin, n1, n2)));
  {
    old_vis := my_vis; old_c := c;

    s := s + 1;
    c := cn;
    call cn := readNext(c);
    call my_vis := intro_readNextTags(c, my_vis);
    if (cn != null) {
      ci := ci + 1;
    }

    // Case 1
    assert {:layer 1} Btwn(next, start, c, t0) && c != t0
      ==> Set_elem(nextInvoc[c], old_vis);
    assert {:layer 1} Btwn(next, start, c, t0) && c != t0
      ==> old_vis == my_vis
      && t0i == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
      && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis)));
    // Case 2  -- restr(lin, my_vis) == append(restr(lin, old_vis), nextInvoc[c])
    assert {:layer 1} Btwn(next, t0, c, null) && next[c] != null
      ==> Seq_restr(lin, my_vis) == Seq_append(Seq_restr(lin, old_vis), nextInvoc[c]);
    assert {:layer 1} Btwn(next, t0, c, null) && next[c] != null
      && Btwn(next, start, old_c, t0) && old_c != t0
      ==> c == t0 && next[old_c] == t0;
    assert {:layer 1} Btwn(next, t0, c, null) && next[c] != null
      && Btwn(next, start, old_c, t0) && old_c != t0
      ==> ci == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)));
    assert {:layer 1} Btwn(next, t0, c, null) && next[c] != null
      ==> ci == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)));
    assert {:layer 1} Btwn(next, t0, c, null) && next[c] != null
      ==> s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis)));

    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} (forall j: Invoc ::
      hb(j, this) ==> Set_subset(vis[j], my_vis));
    assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, my_vis)}
      Set_elem(n1, my_vis) ==> Set_elem(n1, Set_ofSeq(lin)));
    assert {:layer 1} known(c) && (usedFP[c] || queueFP[c]);
    assert {:layer 1} known(cn) && (cn != null ==> next[c] == cn);
    assert {:layer 1} cn == null ==> Btwn(next, t0, c, null);
    assert {:layer 1} known(t0) && t0 != null && Btwn(next, start, t0, null);
    assert {:layer 1} ((cn == null && c == absRefs[ci - 1]) || (cn != null && c == absRefs[ci - 2])) && t0 == absRefs[t0i - 1];
    assert {:layer 1} (Btwn(next, start, c, t0) && c != t0
        && t0i == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
        && (forall n: Invoc :: {Set_elem(n, my_vis)}
          known(nextRef[n]) && invoc_m(n) == Queue.push ==>
          (Set_elem(n, my_vis) <==> Btwn(next, start, nextRef[n], t0) && nextRef[n] != t0))
        && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))
      || (Btwn(next, t0, c, null)
        && ci == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
        && (forall n: Invoc :: {Set_elem(n, my_vis)}
          known(nextRef[n]) && invoc_m(n) == Queue.push ==>
          (Set_elem(n, my_vis) <==> Btwn(next, start, nextRef[n], c)
            && (cn != null || nextRef[n] != c)))
        && ((cn == null && s == ci - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))
          || (cn != null && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))));
    assert {:layer 1} (forall n1, n2: Invoc :: {Seq_ord(lin, n1, n2)} known(nextRef[n2]) ==>
      (Seq_elem(n1, Seq_restr(lin, my_vis)) && Seq_elem(n2, lin) && !Set_elem(n2, my_vis)
      && invoc_m(n2) == Queue.push ==> Seq_ord(lin, n1, n2)));
  }

  // Linearization point.
  call intro_writeLin(this);
  call intro_writeVis(this, my_vis);

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
}

procedure {:yields} {:layer 1} {:refines "size_return_atomic"}
    size_return({:linear "this"} this: Invoc)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  requires {:layer 1} postLP(called, returned, lin, this);
  requires {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  modifies returned;
{
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  assert {:layer 1} postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));

  call intro_writeReturned(this);

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
}
