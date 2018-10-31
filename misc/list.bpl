type Loc;
const null: Loc;

type Heap;
function {:linear "Node"} dom(Heap): [Loc]bool;
function next(Heap): [Loc]Loc;
function data(Heap): [Loc]int;
function {:builtin "MapConst"} MapConstLocBool(bool) : [Loc]bool;

function EmptyLmap(): (Heap);
axiom (dom(EmptyLmap()) == MapConstLocBool(false));

function Add(h: Heap, l: Loc, v: Loc): (Heap);
axiom (forall h: Heap, l: Loc, v: Loc :: dom(Add(h, l, v)) == dom(h)[l:=true] && next(Add(h, l, v)) == next(h)[l := v]);

function Remove(h: Heap, l: Loc): (Heap);
axiom (forall h: Heap, l: Loc :: dom(Remove(h, l)) == dom(h)[l:=false] && next(Remove(h, l)) == next(h));


// Concrete state of implementation
var heap: Heap;
var head: Loc;
var tail: Loc;


// The invariants
function {:inline} Inv(heap: Heap, head: Loc, tail: Loc) : bool
{
  BetweenSet(next(heap), head, null)[head] && BetweenSet(next(heap), head, null)[tail]
    && Subset(BetweenSet(next(heap), head, null), Union(Singleton(null), dom(heap)))
}

// ---------- Primitives/helpers for modifying global state


procedure {:inline 1} alloc(x: Loc)
  modifies heap;
{
  assert !dom(heap)[x];
  heap := Add(heap, x, null);
}

procedure {:inline 1} read_tail() returns (t: Loc)
{
  t := tail;
}

procedure {:inline 1} read_next(x: Loc) returns (y: Loc)
{
  y := next(heap)[x];
}

procedure {:inline 2} cas_next(x, x_old, x_new: Loc)
  returns (res: bool)
  modifies heap;
{
  assert dom(heap)[x];
  if (next(heap)[x] == x_old) {
    heap := Add(heap, x, x_new);
    res := true;
  } else {
    res := false;
  }
}


// ---------- The ADT methods


procedure offer(v: int, x: Loc)
  returns (res: bool)
  requires Inv(heap, head, tail);
  // Assume x_Heap has node at location x with value v
  //  requires dom(x_Heap)[x]; // && data(x_Heap)[x] == v;
  ensures Inv(heap, head, tail);
  modifies heap, tail;
{
  var t, tn: Loc;
  var b: bool;
  assume !BetweenSet(next(heap), head, null)[x] && !dom(heap)[x];

  assert Inv(heap, head, tail);
  call alloc(x);
  assert Inv(heap, head, tail);

  while (true)
    invariant Inv(heap, head, tail);
  {
    call t := read_tail();
    assert Inv(heap, head, tail);

    call tn := read_next(t);

    if (tn == null) {
      assert Inv(heap, head, tail);
      call b := cas_next(t, tn, x);
      if (b) {
        heap := Add(heap, t, x);
        res := true;
  
        assert Inv(heap, head, tail);
        return;
      }
    } else {
      // call b:= cas_tail(t, tn);
      assume tail != null;
      tail := tn;
      assert BetweenSet(next(heap), head, null)[tail];

      assert Inv(heap, head, tail);
    }
  }
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
