// ----------------------------------------
// Reachability axioms from CIVL's Treiber example.
//
// Use options -noinfer -typeEncoding:m -useArrayTheory
// ----------------------------------------

type Loc;
const null: Loc;

type Heap;
function dom(Heap): [Loc]bool;
function next(Heap): [Loc]Loc;
function {:builtin "MapConst"} MapConstBool(bool) : [Loc]bool;

function EmptyHeap(): (Heap);
axiom (dom(EmptyHeap()) == MapConstBool(false));

function Add(h: Heap, l: Loc, v: Loc): (Heap);
axiom (forall h: Heap, l: Loc, v: Loc :: dom(Add(h, l, v)) == dom(h)[l:=true] && next(Add(h, l, v)) == next(h)[l := v]);

function Remove(h: Heap, l: Loc): (Heap);
axiom (forall h: Heap, l: Loc :: dom(Remove(h, l)) == dom(h)[l:=false] && next(Remove(h, l)) == next(h));

// Linearity stuff:

function {:inline} NodeSetCollector(x: [Loc]bool) : [Loc]bool
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

var queue: Heap;
var Used: [Loc]bool;

var head: Loc;
var tail: Loc;


function {:inline} Inv(queue: Heap, head: Loc, tail: Loc) : (bool)
{
  Between(next(queue), head, head, null)
    && Between(next(queue), head, tail, null)
    // && Subset(BtwnSet(next(queue), head, null),
            //  Union(Singleton(null), dom(queue)))
    && tail != null
}


// ---------- Primitives for manipulating ghost state

procedure {:inline 2} TransferToqueue(t: Loc, oldVal: Loc,
    newVal: Loc, l_in:Heap)
  returns (r: bool, l_out:Heap)
  modifies queue;
{
  assert dom(l_in)[newVal];
  if (next(queue)[t] == oldVal) {
    queue := Add(queue, t, newVal);
    l_out := EmptyHeap();
    queue := Add(queue, newVal, next(l_in)[newVal]);
    r := true;
  } else {
    l_out := l_in;
    r := false;
  }
}

// ---------- queue methods:

procedure test1(head: Loc, tail: Loc, c: Loc, x1: Loc)
  requires Between(next(queue), head, head, null)
    && Between(next(queue), head, tail, null)
    && tail != null;
  requires dom(queue)[x1] && next(queue)[x1] == null;
  requires x1 != tail;  // IMP!
  requires Between(next(queue), head, c, null);
  ensures Between(next(queue), head, head, null)
    && Between(next(queue), head, tail, null)
    && tail != null;
  ensures Between(next(queue), head, c, null);
  modifies queue;
{
  var old_q: Heap;
  if (next(queue)[tail] == null) {
    // assert known(head) && known(tail) && known(null) && known(x1) && known(c)
    //   && known(next(queue)[x1])
    //   && knownF(next(queue));

    old_q := queue;
    queue := Add(queue, tail, x1);

    // assert known(head) && known(tail) && known(null) && known(x1)
    //   && knownF(next(queue));

    assert Between(next(queue), head, tail, null);
  } else {
    assume false;
  }
}

procedure test(x: Loc, x_Heap: Heap, c: Loc)
  requires Inv(queue, head, tail);
  requires dom(x_Heap)[x] && next(x_Heap)[x] == null;
  requires Between(next(queue), head, c, null);
  ensures Between(next(queue), head, tail, null);  // TODO this fails
  ensures Between(next(queue), head, head, null)
    // && Between(next(queue), head, tail, null)  // TODO this fails
    // && Subset(BtwnSet(next(queue), head, null),
            //  Union(Singleton(null), dom(queue)))
    && tail != null
    ;
  // ensures Between(next(queue), head, c, null);
  // requires (Used[c] && Between(next(queue), c, c, head))
  //   || Between(next(queue), head, c, null);
  // ensures (Used[c] && Between(next(queue), c, c, head))
  //   || Between(next(queue), head, c, null);
  modifies queue;
{
  var g: bool;
  var t_Heap: Heap;

  // assert known(head) && known(tail) && known(c) && known(x) && known(null)
  //   && knownF(next(queue)) && knownF(next(x_Heap));

  // call g, t_Heap := TransferToqueue(tail, null, x, x_Heap);
  if (next(queue)[tail] == null) {
    queue := Add(queue, tail, x);

    assert Between(next(queue), head, tail, next(queue)[x]);  // TODO this fails

    // assert knownF(next(queue));
    queue := Add(queue, x, next(x_Heap)[x]);

    // assert knownF(next(queue));
  }
}
