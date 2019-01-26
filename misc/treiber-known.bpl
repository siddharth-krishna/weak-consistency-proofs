// ----------------------------------------
// An adaptation of the Treiber stack example from CIVL,
// using the Grasshopper reachability axioms and the
// known() trick to control instantiations.
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

// TODO is this one ever used?
function {:inline} {:linear "Node"} NodeCollector(x: Loc) : [Loc]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "Node"} NodeSetCollector(x: [Loc]bool) : [Loc]bool
{
  x
}


// ---------- Reachability, between, and associated theories

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
// Axioms for Between
//////////////////////////

// reflexive
axiom(forall f: [Loc]Loc, x: Loc :: Between(f, x, x, x));

// step
axiom(forall f: [Loc]Loc, x: Loc :: {f[x]} Between(f, x, f[x], f[x]));

// reach
axiom(forall f: [Loc]Loc, x: Loc, y: Loc :: {f[x], known(y)} Between(f, x, y, y) ==> x == y || Between(f, x, f[x], y));

// cycle
axiom(forall f: [Loc]Loc, x: Loc, y:Loc :: {f[x], known(y)} f[x] == x && Between(f, x, y, y) ==> x == y);

// sandwich
axiom(forall f: [Loc]Loc, x: Loc, y: Loc :: {knownF(f), known(x), known(y)} Between(f, x, y, x) ==> x == y);

// order1
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {knownF(f), known(x), known(y), known(z)} Between(f, x, y, y) && Between(f, x, z, z) ==> Between(f, x, y, z) || Between(f, x, z, y));

// order2
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {knownF(f), known(x), known(y), known(z)} Between(f, x, y, z) ==> Between(f, x, y, y) && Between(f, y, z, z));

// transitive1
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {knownF(f), known(x), known(y), known(z)} Between(f, x, y, y) && Between(f, y, z, z) ==> Between(f, x, z, z));

// transitive2
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc, w: Loc :: {knownF(f), known(x), known(y), known(z), known(w)} Between(f, x, y, z) && Between(f, y, w, z) ==> Between(f, x, y, w) && Between(f, x, w, z));

// transitive3
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc, w: Loc :: {knownF(f), known(x), known(y), known(z), known(w)} Between(f, x, y, z) && Between(f, x, w, y) ==> Between(f, x, w, z) && Between(f, w, y, z));

// relation between Avoiding and Between
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {knownF(f), known(x), known(y), known(z)} Avoiding(f, x, y, z) <==> (Between(f, x, y, z) || (Between(f, x, y, y) && !Between(f, x, z, z))));
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {knownF(f), known(x), known(y), known(z)} Between(f, x, y, z) <==> (Avoiding(f, x, y, z) && Avoiding(f, x, z, z)));

// BWr: grasshopper's update axiom
axiom (forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc, u: Loc, v: Loc :: {f[u := v], known(x), known(y), known(z)}
        Between(f[u := v], x, y, z) <==>
          (Between(f, x, y, z) && Avoiding(f, x, z, u))
          || (u != z && Avoiding(f, x, u, z) && Avoiding(f, v, z, u)
            && (Between(f, x, y, u) || Between(f, v, y, z))));


// ---------- Shared state and invariant

var {:linear "Node"} {:layer 0,2} Stack: Heap;
var {:linear "Node"} {:layer 0,2} Used: [Loc]bool;

var {:layer 0,2} TopOfStack: Loc;


function {:inline} Inv(TopOfStack: Loc, Stack: Heap) : (bool)
{
  Between(next(Stack), TopOfStack, TopOfStack, null)
    && (forall l: Loc :: {Between(next(Stack), TopOfStack, l, null)} known(l) ==>
       (Between(next(Stack), TopOfStack, l, null)
       ==> l == null || dom(Stack)[l]))
    && known(TopOfStack) && known(null) && knownF(next(Stack))
}


// ---------- Primitives for manipulating ghost state

procedure {:atomic} {:layer 1} AtomicReadTopOfStack() returns (v:Loc)
{ v := TopOfStack; assume known(v); }

procedure {:yields} {:layer 0} {:refines "AtomicReadTopOfStack"} ReadTopOfStack() returns (v:Loc);

procedure {:right} {:layer 1} AtomicLoad(i:Loc) returns (v:Loc)
{
  assert dom(Stack)[i] || Used[i];
  if (dom(Stack)[i]) {
    v := next(Stack)[i];
    assume known(v);
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicLoad"} Load(i:Loc) returns (v:Loc);

procedure {:both} {:layer 1} AtomicStore({:linear_in "Node"} l_in:Heap, i:Loc, v:Loc) returns ({:linear "Node"} l_out:Heap)
{ assert dom(l_in)[i]; l_out := Add(l_in, i, v);
  assume knownF(next(l_in)); }

procedure {:yields} {:layer 0} {:refines "AtomicStore"} Store({:linear_in "Node"} l_in:Heap, i:Loc, v:Loc) returns ({:linear "Node"} l_out:Heap);

procedure {:atomic} {:layer 1} AtomicTransferToStack(oldVal: Loc, newVal: Loc, {:linear_in "Node"} l_in:Heap) returns (r: bool, {:linear "Node"} l_out:Heap)
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

procedure {:yields} {:layer 0} {:refines "AtomicTransferToStack"} TransferToStack(oldVal: Loc, newVal: Loc, {:linear_in "Node"} l_in:Heap) returns (r: bool, {:linear "Node"} l_out:Heap);

procedure {:atomic} {:layer 1} AtomicTransferFromStack(oldVal: Loc, newVal: Loc) returns (r: bool)
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

procedure {:yields} {:layer 0} {:refines "AtomicTransferFromStack"} TransferFromStack(oldVal: Loc, newVal: Loc) returns (r: bool);


// ---------- Stack methods:

procedure {:atomic} {:layer 2} atomic_push(x: Loc, {:linear_in "Node"} x_Heap: Heap)
modifies Stack, TopOfStack;
{
  Stack := Add(Stack, x, TopOfStack);
  TopOfStack := x;
  assume known(TopOfStack) && knownF(next(Stack));
}

procedure {:yields} {:layer 1} {:refines "atomic_push"} push(x: Loc, {:linear_in "Node"} x_Heap: Heap)
requires {:layer 1} dom(x_Heap)[x];
requires {:layer 1} Inv(TopOfStack, Stack);
ensures {:layer 1} Inv(TopOfStack, Stack);
{
  var t: Loc;
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

procedure {:atomic} {:layer 2} atomic_pop() returns (t: Loc)
modifies Used, TopOfStack, Stack;
{ assume TopOfStack != null; t := TopOfStack; Used[t] := true; TopOfStack := next(Stack)[t]; Stack := Remove(Stack, t); }

procedure {:yields} {:layer 1} {:refines "atomic_pop"} pop() returns (t: Loc)
requires {:layer 1} Inv(TopOfStack, Stack);
ensures {:layer 1} Inv(TopOfStack, Stack);
{
  var g: bool;
  var x: Loc;

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
