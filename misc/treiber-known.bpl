// ----------------------------------------
// An adaptation of the Treiber stack example from CIVL,
// using the Grasshopper reachability axioms and the
// known() trick to control instantiations.
//
// Also trying to use FP sets for linearity instead of Heaps and dom(Heap).
// Trouble then is that push does not have an atomic equivalent since
// it modifies next many times. TODO have abstract stack on layer 2!
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

// Fields:
var {:layer 0, 1} next: [Ref]Ref;

var {:linear "FP"} {:layer 0, 1} StackFP: [Ref]bool;
var {:linear "FP"} {:layer 0, 1} UsedFP: [Ref]bool;

var {:layer 0, 1} TopOfStack: Ref;


function {:inline} Inv(TopOfStack: Ref, StackFP: [Ref]bool, next: [Ref]Ref) : (bool)
{
  Btwn(next, TopOfStack, TopOfStack, null)
    && (forall l: Ref :: {Btwn(next, TopOfStack, l, null)} known(l) ==>
       (Btwn(next, TopOfStack, l, null)
       ==> l == null || StackFP[l]))
    && known(TopOfStack) && known(null) && knownF(next)
}


// ---------- Primitives for manipulating ghost state

procedure {:atomic} {:layer 1} AtomicReadTopOfStack() returns (v:Ref)
{ v := TopOfStack; }

procedure {:yields} {:layer 0} {:refines "AtomicReadTopOfStack"} ReadTopOfStack() returns (v:Ref);

procedure {:right} {:layer 1} AtomicLoad(i:Ref) returns (v:Ref)
{
  assert StackFP[i] || UsedFP[i];
  // FP can't be passed in because it's a shared variable..
  v := next[i];
  assume known(v);
}

procedure {:yields} {:layer 0} {:refines "AtomicLoad"} Load(i:Ref) returns (v:Ref);

procedure {:both} {:layer 1} AtomicStore({:linear "FP"} FP:[Ref]bool,
    i:Ref, v:Ref)
  modifies next;
{
  assert FP[i];
  next := next[i := v];
  assume knownF(next);
}

procedure {:yields} {:layer 0} {:refines "AtomicStore"}
  Store({:linear "FP"} FP:[Ref]bool, i:Ref, v:Ref);

procedure {:atomic} {:layer 1} AtomicTransferToStack(oldVal: Ref, newVal: Ref, {:linear_in "FP"} l_in:[Ref]bool) returns (r: bool, {:linear "FP"} l_out:[Ref]bool)
modifies TopOfStack, StackFP;
{
  assert l_in[newVal];
  if (oldVal == TopOfStack) {
    TopOfStack := newVal;
    l_out := EmptyHeap();
    StackFP := Add(StackFP, newVal);
    assume known(oldVal) && known(TopOfStack) && known(next[newVal])
      && knownF(next);
    r := true;
  } else {
    l_out := l_in;
    r := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicTransferToStack"} TransferToStack(oldVal: Ref, newVal: Ref, {:linear_in "FP"} l_in:[Ref]bool) returns (r: bool, {:linear "FP"} l_out:[Ref]bool);

procedure {:atomic} {:layer 1} AtomicTransferFromStack(oldVal: Ref, newVal: Ref) returns (r: bool)
modifies TopOfStack, UsedFP, StackFP;
{
  if (oldVal == TopOfStack) {
    TopOfStack := newVal;
    UsedFP[oldVal] := true;
    StackFP := Remove(StackFP, oldVal);
    assume known(oldVal) && known(TopOfStack) && knownF(next);
    r := true;
  }
  else {
    r := false;
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicTransferFromStack"} TransferFromStack(oldVal: Ref, newVal: Ref) returns (r: bool);


// ---------- Stack methods:

procedure {:atomic} {:layer 2} atomic_push(x: Ref, {:linear_in "FP"} x_Heap: [Ref]bool)
modifies next, StackFP, TopOfStack;
{
  // StackFP := Add(StackFP, x);
  // TopOfStack := x;
}

procedure {:yields} {:layer 1} {:refines "atomic_push"} push(x: Ref, {:linear_in "FP"} x_Heap: [Ref]bool)
requires {:layer 1} x_Heap[x];
requires {:layer 1} Inv(TopOfStack, StackFP, next);
ensures {:layer 1} Inv(TopOfStack, StackFP, next);
{
  var t: Ref;
  var g: bool;
  var {:linear "FP"} t_Heap: [Ref]bool;

  yield;
  assert {:layer 1} Inv(TopOfStack, StackFP, next);
  t_Heap := x_Heap;
  while (true)
    invariant {:layer 1} t_Heap == x_Heap && known(x);
    invariant {:layer 1} Inv(TopOfStack, StackFP, next);
  {
    call t := ReadTopOfStack();
    yield;
    assert {:layer 1} Inv(TopOfStack, StackFP, next);
    assert {:layer 1} t_Heap == x_Heap;
    call Store(t_Heap, x, t);
    call g, t_Heap := TransferToStack(t, x, t_Heap);
    if (g) {
      break;
    }
    yield;
    assert {:layer 1} t_Heap == x_Heap;
    assert {:layer 1} Inv(TopOfStack, StackFP, next);
  }
  yield;
  assert {:expand} {:layer 1} Inv(TopOfStack, StackFP, next);
}

procedure {:atomic} {:layer 2} atomic_pop() returns (t: Ref)
modifies UsedFP, TopOfStack, StackFP;
{
  // assume TopOfStack != null; t := TopOfStack; UsedFP[t] := true; TopOfStack := next[t]; StackFP := Remove(StackFP, t);
}

procedure {:yields} {:layer 1} {:refines "atomic_pop"} pop() returns (t: Ref)
requires {:layer 1} Inv(TopOfStack, StackFP, next);
ensures {:layer 1} Inv(TopOfStack, StackFP, next);
{
  var g: bool;
  var x: Ref;

  yield;
  assert {:layer 1} Inv(TopOfStack, StackFP, next);
  while (true)
    invariant {:layer 1} Inv(TopOfStack, StackFP, next);
  {
    call t := ReadTopOfStack();
    yield;
    assert {:layer 1} Inv(TopOfStack, StackFP, next);
    assert {:layer 1} t == null || StackFP[t] || UsedFP[t];
    if (t != null) {
      call x := Load(t);
      call g := TransferFromStack(t, x);
      if (g) {
        break;
      }
    }
    yield;
    assert {:layer 1} Inv(TopOfStack, StackFP, next);
  }
  yield;
  assert {:layer 1} Inv(TopOfStack, StackFP, next);
}
