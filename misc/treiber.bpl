// ----------------------------------------
// An adaptation of the Treiber stack example from CIVL,
// using general Heap and Loc types.
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
axiom(forall S:[Loc]bool, T:[Loc]bool :: {Subset(S,T)} Subset(S,T) || (exists x:Loc :: S[x] && !T[x]));


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

// reflexive
axiom(forall f: [Loc]Loc, x: Loc :: Between(f, x, x, x));

// step
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc, w:Loc :: {Between(f, y, z, w), f[x]} Between(f, x, f[x], f[x]));

// reach
axiom(forall f: [Loc]Loc, x: Loc, y: Loc :: {f[x], Between(f, x, y, y)} Between(f, x, y, y) ==> x == y || Between(f, x, f[x], y));

// cycle
axiom(forall f: [Loc]Loc, x: Loc, y:Loc :: {f[x], Between(f, x, y, y)} f[x] == x && Between(f, x, y, y) ==> x == y);

// sandwich
axiom(forall f: [Loc]Loc, x: Loc, y: Loc :: {Between(f, x, y, x)} Between(f, x, y, x) ==> x == y);

// order1
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {Between(f, x, y, y), Between(f, x, z, z)} Between(f, x, y, y) && Between(f, x, z, z) ==> Between(f, x, y, z) || Between(f, x, z, y));

// order2
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {Between(f, x, y, z)} Between(f, x, y, z) ==> Between(f, x, y, y) && Between(f, y, z, z));

// transitive1
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {Between(f, x, y, y), Between(f, y, z, z)} Between(f, x, y, y) && Between(f, y, z, z) ==> Between(f, x, z, z));

// transitive2
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc, w: Loc :: {Between(f, x, y, z), Between(f, y, w, z)} Between(f, x, y, z) && Between(f, y, w, z) ==> Between(f, x, y, w) && Between(f, x, w, z));

// transitive3
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc, w: Loc :: {Between(f, x, y, z), Between(f, x, w, y)} Between(f, x, y, z) && Between(f, x, w, y) ==> Between(f, x, w, z) && Between(f, w, y, z));

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.
// It cannot be proved using the rest of the axioms.
axiom(forall f: [Loc]Loc, u:Loc, x: Loc :: {Between(f, u, x, x)} Between(f, u, x, x) ==> Between(f, u, u, x));

// relation between Avoiding and Between
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {Avoiding(f, x, y, z)} Avoiding(f, x, y, z) <==> (Between(f, x, y, z) || (Between(f, x, y, y) && !Between(f, x, z, z))));
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {Between(f, x, y, z)} Between(f, x, y, z) <==> (Avoiding(f, x, y, z) && Avoiding(f, x, z, z)));

// update
axiom(forall f: [Loc]Loc, u: Loc, v: Loc, x: Loc, p: Loc, q: Loc :: {Avoiding(f[p := q], u, v, x)} Avoiding(f[p := q], u, v, x) <==> ((Avoiding(f, u, v, p) && Avoiding(f, u, v, x)) || (Avoiding(f, u, p, x) && p != x && Avoiding(f, q, v, p) && Avoiding(f, q, v, x))));

axiom (forall f: [Loc]Loc, p: Loc, q: Loc, u: Loc, w: Loc :: {BetweenSet(f[p := q], u, w)} Avoiding(f, u, w, p) ==> Equal(BetweenSet(f[p := q], u, w), BetweenSet(f, u, w)));
axiom (forall f: [Loc]Loc, p: Loc, q: Loc, u: Loc, w: Loc :: {BetweenSet(f[p := q], u, w)} p != w && Avoiding(f, u, p, w) && Avoiding(f, q, w, p) ==> Equal(BetweenSet(f[p := q], u, w), Union(BetweenSet(f, u, p), BetweenSet(f, q, w))));
axiom (forall f: [Loc]Loc, p: Loc, q: Loc, u: Loc, w: Loc :: {BetweenSet(f[p := q], u, w)} Avoiding(f, u, w, p) || (p != w && Avoiding(f, u, p, w) && Avoiding(f, q, w, p)) || Equal(BetweenSet(f[p := q], u, w), Empty()));


// ---------- Shared state and invariant

var {:linear "Node"} {:layer 0,2} Stack: Heap;
var {:linear "Node"} {:layer 0,2} Used: [Loc]bool;

var {:layer 0,2} TopOfStack: Loc;


function {:inline} Inv(TopOfStack: Loc, Stack: Heap) : (bool)
{
  Between(next(Stack), TopOfStack, TopOfStack, null)
    && (forall l: Loc :: {Between(next(Stack), TopOfStack, l, null)}
       (Between(next(Stack), TopOfStack, l, null)
       ==> l == null || dom(Stack)[l]))
}


// ---------- Primitives for manipulating ghost state

procedure {:atomic} {:layer 1} AtomicReadTopOfStack() returns (v:Loc)
{ v := TopOfStack; }

procedure {:yields} {:layer 0} {:refines "AtomicReadTopOfStack"} ReadTopOfStack() returns (v:Loc);

procedure {:right} {:layer 1} AtomicLoad(i:Loc) returns (v:Loc)
{
  assert dom(Stack)[i] || Used[i];
  if (dom(Stack)[i]) {
    v := next(Stack)[i];
  }
}

procedure {:yields} {:layer 0} {:refines "AtomicLoad"} Load(i:Loc) returns (v:Loc);

procedure {:both} {:layer 1} AtomicStore({:linear_in "Node"} l_in:Heap, i:Loc, v:Loc) returns ({:linear "Node"} l_out:Heap)
{ assert dom(l_in)[i]; l_out := Add(l_in, i, v); }

procedure {:yields} {:layer 0} {:refines "AtomicStore"} Store({:linear_in "Node"} l_in:Heap, i:Loc, v:Loc) returns ({:linear "Node"} l_out:Heap);

procedure {:atomic} {:layer 1} AtomicTransferToStack(oldVal: Loc, newVal: Loc, {:linear_in "Node"} l_in:Heap) returns (r: bool, {:linear "Node"} l_out:Heap)
modifies TopOfStack, Stack;
{
  assert dom(l_in)[newVal];
  if (oldVal == TopOfStack) {
    TopOfStack := newVal;
    l_out := EmptyHeap();
    Stack := Add(Stack, newVal, next(l_in)[newVal]);
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
  assert {:layer 1} Inv(TopOfStack, Stack);
  t_Heap := x_Heap;
  while (true)
    invariant {:layer 1} dom(t_Heap) == dom(x_Heap);
    invariant {:layer 1} Inv(TopOfStack, Stack);
  {
    call t := ReadTopOfStack();
    yield;
    assert {:layer 1} Inv(TopOfStack, Stack);
    assert {:layer 1} dom(t_Heap) == dom(x_Heap);
    call t_Heap := Store(t_Heap, x, t);
    call g, t_Heap := TransferToStack(t, x, t_Heap);
    if (g) {
      break;
    }
    yield;
    assert {:layer 1} dom(t_Heap) == dom(x_Heap);
    assert {:layer 1} Inv(TopOfStack, Stack);
  }
  yield;
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
  assert {:layer 1} Inv(TopOfStack, Stack);
  while (true)
    invariant {:layer 1} Inv(TopOfStack, Stack);
  {
    call t := ReadTopOfStack();
    yield;
    assert {:layer 1} Inv(TopOfStack, Stack);
    assert {:layer 1} t == null || dom(Stack)[t] || Used[t];
    if (t != null) {
      call x := Load(t);
      call g := TransferFromStack(t, x);
      if (g) {
        break;
      }
    }
    yield;
    assert {:layer 1} Inv(TopOfStack, Stack);
  }
  yield;
  assert {:layer 1} Inv(TopOfStack, Stack);
}
