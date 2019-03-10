// ----------------------------------------
// Reachability axioms from CIVL's Treiber example.
//
// Use options -noinfer -typeEncoding:m -useArrayTheory
// ----------------------------------------

type Ref;
const null: Ref;

type Heap;
function dom(Heap): [Ref]bool;
function next(Heap): [Ref]Ref;
function {:builtin "MapConst"} MapConstBool(bool) : [Ref]bool;

function EmptyHeap(): (Heap);
axiom (dom(EmptyHeap()) == MapConstBool(false));

function Add(h: Heap, l: Ref, v: Ref): (Heap);
axiom (forall h: Heap, l: Ref, v: Ref :: dom(Add(h, l, v)) == dom(h)[l:=true] && next(Add(h, l, v)) == next(h)[l := v]);

function Remove(h: Heap, l: Ref): (Heap);
axiom (forall h: Heap, l: Ref :: dom(Remove(h, l)) == dom(h)[l:=false] && next(Remove(h, l)) == next(h));

// Linearity stuff:

function {:inline} NodeSetCollector(x: [Ref]bool) : [Ref]bool
{
  x
}


// ---------- Reachability, between, and associated theories

function Equal([Ref]bool, [Ref]bool) returns (bool);
function Subset([Ref]bool, [Ref]bool) returns (bool);

function Empty() returns ([Ref]bool);
function Singleton(Ref) returns ([Ref]bool);
function Union([Ref]bool, [Ref]bool) returns ([Ref]bool);

axiom(forall x:Ref :: !Empty()[x]);

axiom(forall x:Ref, y:Ref :: {Singleton(y)[x]} Singleton(y)[x] <==> x == y);
axiom(forall y:Ref :: {Singleton(y)} Singleton(y)[y]);

axiom(forall x:Ref, S:[Ref]bool, T:[Ref]bool :: {Union(S,T)[x]}{Union(S,T),S[x]}{Union(S,T),T[x]} Union(S,T)[x] <==> S[x] || T[x]);

axiom(forall S:[Ref]bool, T:[Ref]bool :: {Equal(S,T)} Equal(S,T) <==> Subset(S,T) && Subset(T,S));
axiom(forall x:Ref, S:[Ref]bool, T:[Ref]bool :: {S[x],Subset(S,T)}{T[x],Subset(S,T)} S[x] && Subset(S,T) ==> T[x]);
axiom(forall S:[Ref]bool, T:[Ref]bool :: {Subset(S,T)} Subset(S,T) || (exists x:Ref :: S[x] && !T[x]));


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

// reflexive
axiom(forall f: [Ref]Ref, x: Ref :: Btwn(f, x, x, x));

// step
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, w:Ref :: {Btwn(f, y, z, w), f[x]} Btwn(f, x, f[x], f[x]));

// reach
axiom(forall f: [Ref]Ref, x: Ref, y: Ref :: {f[x], Btwn(f, x, y, y)} Btwn(f, x, y, y) ==> x == y || Btwn(f, x, f[x], y));

// cycle
axiom(forall f: [Ref]Ref, x: Ref, y:Ref :: {f[x], Btwn(f, x, y, y)} f[x] == x && Btwn(f, x, y, y) ==> x == y);

// sandwich
axiom(forall f: [Ref]Ref, x: Ref, y: Ref :: {Btwn(f, x, y, x)} Btwn(f, x, y, x) ==> x == y);

// order1
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {Btwn(f, x, y, y), Btwn(f, x, z, z)} Btwn(f, x, y, y) && Btwn(f, x, z, z) ==> Btwn(f, x, y, z) || Btwn(f, x, z, y));

// order2
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {Btwn(f, x, y, z)} Btwn(f, x, y, z) ==> Btwn(f, x, y, y) && Btwn(f, y, z, z));

// transitive1
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {Btwn(f, x, y, y), Btwn(f, y, z, z)} Btwn(f, x, y, y) && Btwn(f, y, z, z) ==> Btwn(f, x, z, z));

// transitive2
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, w: Ref :: {Btwn(f, x, y, z), Btwn(f, y, w, z)} Btwn(f, x, y, z) && Btwn(f, y, w, z) ==> Btwn(f, x, y, w) && Btwn(f, x, w, z));

// transitive3
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, w: Ref :: {Btwn(f, x, y, z), Btwn(f, x, w, y)} Btwn(f, x, y, z) && Btwn(f, x, w, y) ==> Btwn(f, x, w, z) && Btwn(f, w, y, z));

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.
// It cannot be proved using the rest of the axioms.
axiom(forall f: [Ref]Ref, u:Ref, x: Ref :: {Btwn(f, u, x, x)} Btwn(f, u, x, x) ==> Btwn(f, u, u, x));

// relation between ReachW and Btwn
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {ReachW(f, x, y, z)} ReachW(f, x, y, z) <==> (Btwn(f, x, y, z) || (Btwn(f, x, y, y) && !Btwn(f, x, z, z))));
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {Btwn(f, x, y, z)} Btwn(f, x, y, z) <==> (ReachW(f, x, y, z) && ReachW(f, x, z, z)));

// update
axiom(forall f: [Ref]Ref, u: Ref, v: Ref, x: Ref, p: Ref, q: Ref :: {ReachW(f[p := q], u, v, x)} ReachW(f[p := q], u, v, x) <==> ((ReachW(f, u, v, p) && ReachW(f, u, v, x)) || (ReachW(f, u, p, x) && p != x && ReachW(f, q, v, p) && ReachW(f, q, v, x))));

axiom (forall f: [Ref]Ref, p: Ref, q: Ref, u: Ref, w: Ref :: {BtwnSet(f[p := q], u, w)} ReachW(f, u, w, p) ==> Equal(BtwnSet(f[p := q], u, w), BtwnSet(f, u, w)));
axiom (forall f: [Ref]Ref, p: Ref, q: Ref, u: Ref, w: Ref :: {BtwnSet(f[p := q], u, w)} p != w && ReachW(f, u, p, w) && ReachW(f, q, w, p) ==> Equal(BtwnSet(f[p := q], u, w), Union(BtwnSet(f, u, p), BtwnSet(f, q, w))));
axiom (forall f: [Ref]Ref, p: Ref, q: Ref, u: Ref, w: Ref :: {BtwnSet(f[p := q], u, w)} ReachW(f, u, w, p) || (p != w && ReachW(f, u, p, w) && ReachW(f, q, w, p)) || Equal(BtwnSet(f[p := q], u, w), Empty()));


// ---------- Shared state and invariant

var queue: Heap;
var Used: [Ref]bool;

var head: Ref;
var tail: Ref;


function {:inline} Inv(queue: Heap, head: Ref, tail: Ref) : (bool)
{
  Btwn(next(queue), head, head, null)
    && Btwn(next(queue), head, tail, null)
    // && Subset(BtwnSet(next(queue), head, null),
            //  Union(Singleton(null), dom(queue)))
    && tail != null
}


// ---------- Primitives for manipulating ghost state

procedure {:inline 2} TransferToqueue(t: Ref, oldVal: Ref,
    newVal: Ref, l_in:Heap)
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

procedure test1(head: Ref, tail: Ref, c: Ref, x1: Ref)
  requires Btwn(next(queue), head, head, null)
    && Btwn(next(queue), head, tail, null)
    && tail != null;
  requires dom(queue)[x1] && next(queue)[x1] == null;
  requires x1 != tail;  // IMP!
  requires Btwn(next(queue), head, c, null);
  ensures Btwn(next(queue), head, head, null)
    && Btwn(next(queue), head, tail, null)
    && tail != null;
  ensures Btwn(next(queue), head, c, null);
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

    assert Btwn(next(queue), head, tail, null);
  } else {
    assume false;
  }
}

procedure test(x: Ref, x_Heap: Heap, c: Ref)
  requires Inv(queue, head, tail);
  requires dom(x_Heap)[x] && next(x_Heap)[x] == null;
  requires !Btwn(next(queue), head, x, null); // From linearity
  requires Btwn(next(queue), head, c, null);
  ensures Btwn(next(queue), head, tail, null);  // TODO this fails
  ensures Btwn(next(queue), head, head, null)
    // && Btwn(next(queue), head, tail, null)  // TODO this fails
    // && Subset(BtwnSet(next(queue), head, null),
            //  Union(Singleton(null), dom(queue)))
    && tail != null
    ;
  // ensures Btwn(next(queue), head, c, null);
  // requires (Used[c] && Btwn(next(queue), c, c, head))
  //   || Btwn(next(queue), head, c, null);
  // ensures (Used[c] && Btwn(next(queue), c, c, head))
  //   || Btwn(next(queue), head, c, null);
  modifies queue;
{
  var g: bool;
  var t_Heap: Heap;

  // assert known(head) && known(tail) && known(c) && known(x) && known(null)
  //   && knownF(next(queue)) && knownF(next(x_Heap));

  // call g, t_Heap := TransferToqueue(tail, null, x, x_Heap);
  if (next(queue)[tail] == null) {
    queue := Add(queue, tail, x);

    // assert knownF(next(queue));
    queue := Add(queue, x, next(x_Heap)[x]);

    // assert knownF(next(queue));
  }
}

procedure test2(x: Ref, x_Heap: Heap, c: Ref)
  requires Inv(queue, head, tail);
  requires dom(x_Heap)[x] && next(x_Heap)[x] == null;
  requires x != null && !dom(queue)[x];
  requires Equal(BtwnSet(next(queue), head, null),
             Union(Singleton(null), dom(queue)));
  ensures !Btwn(next(queue), head, x, null); // From linearity
{}