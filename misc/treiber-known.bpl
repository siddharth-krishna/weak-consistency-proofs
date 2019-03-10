// ----------------------------------------
// An adaptation of the Treiber stack example from CIVL,
// using the Grasshopper reachability axioms and the
// known() trick to control instantiations.
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

// TODO is this one ever used?
function {:inline} {:linear "Node"} NodeCollector(x: Ref) : [Ref]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "Node"} NodeSetCollector(x: [Ref]bool) : [Ref]bool
{
  x
}


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

var {:linear "Node"} {:layer 0,2} Stack: Heap;
var {:linear "Node"} {:layer 0,2} Used: [Ref]bool;

var {:layer 0,2} TopOfStack: Ref;


function {:inline} Inv(TopOfStack: Ref, Stack: Heap) : (bool)
{
  Btwn(next(Stack), TopOfStack, TopOfStack, null)
    && (forall l: Ref :: {Btwn(next(Stack), TopOfStack, l, null)} known(l) ==>
       (Btwn(next(Stack), TopOfStack, l, null)
       ==> l == null || dom(Stack)[l]))
    && known(TopOfStack) && known(null) && knownF(next(Stack))
}


// ---------- Primitives for manipulating ghost state

procedure {:atomic} {:layer 1} AtomicReadTopOfStack() returns (v:Ref)
{ v := TopOfStack; assume known(v); }

procedure {:yields} {:layer 0} {:refines "AtomicReadTopOfStack"} ReadTopOfStack() returns (v:Ref);

procedure {:right} {:layer 1} AtomicLoad(i:Ref) returns (v:Ref)
{
  assert dom(Stack)[i] || Used[i];
  if (dom(Stack)[i]) {
    v := next(Stack)[i];
    assume known(v);
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicLoad"} Load(i:Ref) returns (v:Ref);

procedure {:both} {:layer 1} AtomicStore({:linear_in "Node"} l_in:Heap, i:Ref, v:Ref) returns ({:linear "Node"} l_out:Heap)
{ assert dom(l_in)[i]; l_out := Add(l_in, i, v);
  assume knownF(next(l_in)); }

procedure {:yields} {:layer 0} {:refines "AtomicStore"} Store({:linear_in "Node"} l_in:Heap, i:Ref, v:Ref) returns ({:linear "Node"} l_out:Heap);

procedure {:atomic} {:layer 1} AtomicTransferToStack(oldVal: Ref, newVal: Ref, {:linear_in "Node"} l_in:Heap) returns (r: bool, {:linear "Node"} l_out:Heap)
modifies TopOfStack, Stack;
{
  assert dom(l_in)[newVal];
  if (oldVal == TopOfStack) {
    TopOfStack := newVal;
    l_out := EmptyHeap();
    Stack := Add(Stack, newVal, next(l_in)[newVal]);
    assume known(oldVal) && known(TopOfStack) && known(next(l_in)[newVal])
      && knownF(next(Stack));
    r := true;
  } else {
    l_out := l_in;
    r := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicTransferToStack"} TransferToStack(oldVal: Ref, newVal: Ref, {:linear_in "Node"} l_in:Heap) returns (r: bool, {:linear "Node"} l_out:Heap);

procedure {:atomic} {:layer 1} AtomicTransferFromStack(oldVal: Ref, newVal: Ref) returns (r: bool)
modifies TopOfStack, Used, Stack;
{
  if (oldVal == TopOfStack) {
    TopOfStack := newVal;
    Used[oldVal] := true;
    Stack := Remove(Stack, oldVal);
    assume known(oldVal) && known(TopOfStack) && knownF(next(Stack));
    r := true;
  }
  else {
    r := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicTransferFromStack"} TransferFromStack(oldVal: Ref, newVal: Ref) returns (r: bool);


// ---------- Stack methods:

procedure {:atomic} {:layer 2} atomic_push(x: Ref, {:linear_in "Node"} x_Heap: Heap)
modifies Stack, TopOfStack;
{
  Stack := Add(Stack, x, TopOfStack);
  TopOfStack := x;
  assume known(TopOfStack) && knownF(next(Stack));
}

procedure {:yields} {:layer 1} {:refines "atomic_push"} push(x: Ref, {:linear_in "Node"} x_Heap: Heap)
requires {:layer 1} dom(x_Heap)[x];
requires {:layer 1} Inv(TopOfStack, Stack);
ensures {:layer 1} Inv(TopOfStack, Stack);
{
  var t: Ref;
  var g: bool;
  var {:linear "Node"} t_Heap: Heap;

  yield;
  assert {:layer 1} known(x) && known(t);
  assert {:layer 1} Inv(TopOfStack, Stack);
  t_Heap := x_Heap;
  while (true)
    invariant {:layer 1} dom(t_Heap) == dom(x_Heap) && known(x) && known(t);
    invariant {:layer 1} Inv(TopOfStack, Stack);
  {
    call t := ReadTopOfStack();
    yield;
    assert {:layer 1} known(x) && known(t);
    assert {:layer 1} Inv(TopOfStack, Stack);
    assert {:layer 1} dom(t_Heap) == dom(x_Heap);
    call t_Heap := Store(t_Heap, x, t);
    call g, t_Heap := TransferToStack(t, x, t_Heap);
    assert {:layer 1} known(x) && known(t);
    if (g) {
      break;
    }
    yield;
    assert {:layer 1} known(x) && known(t);
    assert {:layer 1} dom(t_Heap) == dom(x_Heap);
    assert {:layer 1} Inv(TopOfStack, Stack);
  }
  yield;
  assert {:layer 1} known(x) && known(t);
  assert {:expand} {:layer 1} Inv(TopOfStack, Stack);
}

procedure {:atomic} {:layer 2} atomic_pop() returns (t: Ref)
modifies Used, TopOfStack, Stack;
{ assume TopOfStack != null; t := TopOfStack; Used[t] := true; TopOfStack := next(Stack)[t]; Stack := Remove(Stack, t); }

procedure {:yields} {:layer 1} {:refines "atomic_pop"} pop() returns (t: Ref)
requires {:layer 1} Inv(TopOfStack, Stack);
ensures {:layer 1} Inv(TopOfStack, Stack);
{
  var g: bool;
  var x: Ref;

  yield;
  assert {:layer 1} known(x) && known(t);
  assert {:layer 1} Inv(TopOfStack, Stack);
  while (true)
    invariant {:layer 1} known(x) && known(t);
    invariant {:layer 1} Inv(TopOfStack, Stack);
  {
    call t := ReadTopOfStack();
    yield;
    assert {:layer 1} known(x) && known(t);
    assert {:layer 1} Inv(TopOfStack, Stack);
    assert {:layer 1} t == null || dom(Stack)[t] || Used[t];
    if (t != null) {
      call x := Load(t);
      call g := TransferFromStack(t, x);
      assert {:layer 1} known(x) && known(t);
      if (g) {
        break;
      }
    }
    yield;
    assert {:layer 1} known(x) && known(t);
    assert {:layer 1} Inv(TopOfStack, Stack);
  }
  yield;
  assert {:layer 1} known(x) && known(t);
  assert {:layer 1} Inv(TopOfStack, Stack);
}
