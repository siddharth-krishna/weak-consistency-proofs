// ----------------------------------------
// A simple queue implementation
// based on the Michael-Scott queue.
// Assumes GC, so does not free dequeued nodes.
// Also uses the simplified heap encoding from CIVL's Treiber example.
//
// Use options -noinfer -typeEncoding:m -useArrayTheory
// ----------------------------------------

type Loc;
const null: Loc;

type Heap;
function {:linear "Node"} dom(Heap): [Loc]bool;
function next(Heap): [Loc]Loc;
function {:builtin "MapConst"} MapConstBool(bool) : [Loc]bool;

function EmptyHeap(): (Heap);
axiom (dom(EmptyHeap()) == MapConstBool(false));

function Add(h: Heap, l: Loc, v: Loc): (Heap);
axiom (forall h: Heap, l: Loc, v: Loc :: dom(Add(h, l, v)) == dom(h)[l:=true] && next(Add(h, l, v)) == next(h)[l := v]);

function Remove(h: Heap, l: Loc): (Heap);
axiom (forall h: Heap, l: Loc :: dom(Remove(h, l)) == dom(h)[l:=false] && next(Remove(h, l)) == next(h));

// Linearity stuff:

function {:inline} {:linear "Node"} NodeSetCollector(x: [Loc]bool) : [Loc]bool
{
  x
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
axiom(forall S:[Loc]bool, T:[Loc]bool :: {Subset(S,T)} Subset(S,T) || (exists x:Loc :: known(x) && S[x] && !T[x]));


// Predicates used to control the triggers on the below axioms
function known(x: Loc) : bool;
function knownF(f: [Loc]Loc) : bool;
axiom(forall x: Loc :: {known(x)} known(x));
axiom(forall f: [Loc]Loc :: {knownF(f)} knownF(f));

 
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

// read null
axiom (forall f: [Loc]Loc :: f[null] == null);

// reflexive
axiom(forall f: [Loc]Loc, x: Loc :: Between(f, x, x, x));

// step
axiom(forall f: [Loc]Loc, x: Loc :: {f[x]} Between(f, x, f[x], f[x]));

// reach
axiom(forall f: [Loc]Loc, x: Loc, y: Loc :: {f[x], known(y)} Between(f, x, y, y) ==> x == y || Between(f, x, f[x], y));

// cycle
axiom(forall f: [Loc]Loc, x: Loc, y:Loc :: {f[x], known(y)} f[x] == x && Between(f, x, y, y) ==> x == y);

// sandwich
axiom(forall f: [Loc]Loc, x: Loc, y: Loc :: {knownF(f), known(x), known(y), Between(f, x, y, x)} Between(f, x, y, x) ==> x == y);

// order1
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {knownF(f), known(x), known(y), known(z), Between(f, x, y, y), Between(f, x, z, z)} Between(f, x, y, y) && Between(f, x, z, z) ==> Between(f, x, y, z) || Between(f, x, z, y));

// order2
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {knownF(f), known(x), known(y), known(z), Between(f, x, y, z)} Between(f, x, y, z) ==> Between(f, x, y, y) && Between(f, y, z, z));

// transitive1
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {knownF(f), known(x), known(y), known(z), Between(f, x, y, y), Between(f, y, z, z)} Between(f, x, y, y) && Between(f, y, z, z) ==> Between(f, x, z, z));

// transitive2
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc, w: Loc :: {knownF(f), known(x), known(y), known(z), known(w), Between(f, x, y, z), Between(f, y, w, z)} Between(f, x, y, z) && Between(f, y, w, z) ==> Between(f, x, y, w) && Between(f, x, w, z));

// transitive3
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc, w: Loc :: {knownF(f), known(x), known(y), known(z), known(w), Between(f, x, y, z), Between(f, x, w, y)} Between(f, x, y, z) && Between(f, x, w, y) ==> Between(f, x, w, z) && Between(f, w, y, z));

// relation between Avoiding and Between
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {knownF(f), known(x), known(y), known(z), Avoiding(f, x, y, z)} Avoiding(f, x, y, z) <==> (Between(f, x, y, z) || (Between(f, x, y, y) && !Between(f, x, z, z))));
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {knownF(f), known(x), known(y), known(z), Between(f, x, y, z)} Between(f, x, y, z) <==> (Avoiding(f, x, y, z) && Avoiding(f, x, z, z)));

// btwn_write: grasshopper's update axiom
axiom (forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc, u: Loc, v: Loc :: {f[u := v], known(x), known(y), known(z), Between(f[u := v], x, y, z)}
        u != null ==>
          (Between(f[u := v], x, y, z) <==>
          (Between(f, x, y, z) && Avoiding(f, x, z, u))
          || (u != z && Avoiding(f, x, u, z) && Avoiding(f, v, z, u)
            && (Between(f, x, y, u) || Between(f, v, y, z)))));


// ---------- Shared state and invariant

var {:linear "Node"} {:layer 0,2} queue: Heap;
var {:linear "Node"} {:layer 0,2} Used: [Loc]bool;

var {:layer 0,2} head: Loc;
var {:layer 0,2} tail: Loc;


function {:inline} Inv(queue: Heap, head: Loc, tail: Loc) : (bool)
{
  Between(next(queue), head, head, null)
    && Between(next(queue), head, tail, null)
    && Equal(BetweenSet(next(queue), head, null),
             Union(Singleton(null), dom(queue)))
    && tail != null
    && known(head) && known(tail) && known(null) && knownF(next(queue))
}


// ---------- Primitives for manipulating ghost state

procedure {:atomic} {:layer 1} AtomicReadhead() returns (v:Loc)
{ v := head; }

procedure {:yields} {:layer 0} {:refines "AtomicReadhead"} Readhead() returns (v:Loc);

procedure {:atomic} {:layer 1} AtomicReadtail() returns (v:Loc)
{ v := tail; }

procedure {:yields} {:layer 0} {:refines "AtomicReadtail"} Readtail() returns (v:Loc);

procedure {:atomic} {:layer 1} AtomicLoad(i:Loc) returns (v:Loc)
{
  assert dom(queue)[i] || Used[i];
  if (dom(queue)[i]) {
    v := next(queue)[i];
    assume known(v);
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicLoad"} Load(i:Loc) returns (v:Loc);

procedure {:both} {:layer 1} AtomicStore({:linear_in "Node"} l_in:Heap, i:Loc, v:Loc) returns ({:linear "Node"} l_out:Heap)
{ assert dom(l_in)[i]; l_out := Add(l_in, i, v); assume knownF(next(l_in)); }

procedure {:yields} {:layer 0} {:refines "AtomicStore"} Store({:linear_in "Node"} l_in:Heap, i:Loc, v:Loc) returns ({:linear "Node"} l_out:Heap);


procedure {:atomic} {:layer 1} AtomicTransferToqueue(t: Loc, oldVal: Loc,
    newVal: Loc, {:linear_in "Node"} l_in:Heap)
  returns (r: bool, {:linear "Node"} l_out:Heap)
  modifies queue;
{
  assert dom(l_in)[newVal];
  if (next(queue)[t] == oldVal) {
    queue := Add(queue, t, newVal);
    l_out := EmptyHeap();
    queue := Add(queue, newVal, next(l_in)[newVal]);
    assume known(oldVal) && known(newVal) && known(next(l_in)[newVal]) && knownF(next(queue));
    r := true;
  } else {
    l_out := l_in;
    r := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicTransferToqueue"}
  TransferToqueue(t: Loc, oldVal: Loc, newVal: Loc,
                  {:linear_in "Node"} l_in:Heap)
  returns (r: bool, {:linear "Node"} l_out:Heap);

procedure {:atomic} {:layer 1} AtomicTransferFromqueue(oldVal: Loc, newVal: Loc) returns (r: bool)
  modifies head, Used, queue;
{
  if (oldVal == head) {
    head := newVal;
    Used[oldVal] := true;
    queue := Remove(queue, oldVal);
    assume known(oldVal) && known(head) && knownF(next(queue));
    r := true;
  }
  else {
    r := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicTransferFromqueue"} TransferFromqueue(oldVal: Loc, newVal: Loc) returns (r: bool);


// ---------- queue methods:

procedure {:atomic} {:layer 2} atomic_pop() returns (t: Loc)
  modifies Used, head, queue;
{
  assume head != null;
  t := head;
  Used[t] := true;
  head := next(queue)[t];
  queue := Remove(queue, t);
  assume known(head) && knownF(next(queue));
}

procedure {:yields} {:layer 1} {:refines "atomic_pop"} pop() returns (h: Loc)
requires {:layer 1} Inv(queue, head, tail);
ensures {:layer 1} Inv(queue, head, tail);
{
  var g: bool;
  var t, x: Loc;

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


procedure {:atomic} {:layer 2} atomic_push(x: Loc,
 {:linear_in "Node"} x_Heap: Heap)
 modifies queue, tail;
{
  if (next(queue)[tail] == null) {
    queue := Add(queue, tail, x);
    queue := Add(queue, x, null);
  }
  // tail := x;
}

procedure {:yields} {:layer 1} {:refines "atomic_push"} push(x: Loc, {:linear_in "Node"} x_Heap: Heap)
  requires {:layer 1} dom(x_Heap)[x] && next(x_Heap)[x] == null;
  requires {:layer 1} Inv(queue, head, tail);
  ensures {:layer 1} Inv(queue, head, tail);
{
  var t, tn: Loc;
  var g: bool;
  var {:linear "Node"} t_Heap: Heap;

  yield;
  assert {:layer 1} Inv(queue, head, tail);
  assert {:layer 1} known(t) && known(tn);
  t_Heap := x_Heap;
  while (true)
    invariant {:layer 1} dom(t_Heap) == dom(x_Heap);
    invariant {:layer 1} next(t_Heap)[x] == null; // TODO needed?
    invariant {:layer 1} Inv(queue, head, tail);
    invariant {:layer 1} known(t) && known(tn);
  {
    call t := Readtail();
    yield;
    assert {:layer 1} Inv(queue, head, tail);
    assert {:layer 1} known(t) && known(tn);
    assert {:layer 1} dom(t_Heap) == dom(x_Heap);
    assert {:layer 1} next(t_Heap)[x] == null;
    assert {:layer 1} t != null && (Between(next(queue), head, t, null)
      || Used[t]);
    assert {:layer 1} next(queue)[t] == null ==> t == tail;

    call tn := Load(t);
    yield;
    assert {:layer 1} Inv(queue, head, tail);
    assert {:layer 1} known(t) && known(tn);
    assert {:layer 1} dom(t_Heap) == dom(x_Heap);
    assert {:layer 1} next(t_Heap)[x] == null;
    assert {:layer 1} t != null && (Between(next(queue), head, t, null)
      || Used[t]);
    assert {:layer 1} next(queue)[t] == null ==> t == tail;

    if (tn == null) {
      call g, t_Heap := TransferToqueue(t, tn, x, t_Heap);
      if (g) {
        break;
      }
    } // TODO else cas tail
    yield;
    assert {:layer 1} dom(t_Heap) == dom(x_Heap);
    assert {:layer 1} Inv(queue, head, tail);
    assert {:layer 1} known(t) && known(tn);
  }
  yield;
  assert {:layer 1} known(head) && known(tail) && known(null) && knownF(next(queue));
  assert {:layer 1} Between(next(queue), head, head, null);
  assert {:layer 1} Between(next(queue), head, tail, null);
  assert {:layer 1} Equal(BetweenSet(next(queue), head, null),
             Union(Singleton(null), dom(queue)));
  assert {:layer 1} tail != null;
  assert {:expand} {:layer 1} Inv(queue, head, tail);
}
