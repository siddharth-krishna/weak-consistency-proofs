// ----------------------------------------
// Reachability axioms from Grasshopper.
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

// read null  // TODO UNSOUND!! Instead, manually assume this for initial fields
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

// btwn_write: grasshopper's update axiom
axiom (forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc, u: Loc, v: Loc :: {f[u := v], known(x), known(y), known(z)}
        u != null ==>
          (Between(f[u := v], x, y, z) <==>
          (Between(f, x, y, z) && Avoiding(f, x, z, u))
          || (u != z && Avoiding(f, x, u, z) && Avoiding(f, v, z, u)
            && (Between(f, x, y, u) || Between(f, v, y, z)))));


// ---------- Shared state and invariant

var queue: Heap;
var Used: [Loc]bool;

var head: Loc;
var tail: Loc;


function {:inline} Inv(queue: Heap, head: Loc, tail: Loc) : (bool)
{
  Between(next(queue), head, head, null)
    && Between(next(queue), head, tail, null)
    && Equal(BetweenSet(next(queue), head, null),
             Union(Singleton(null), dom(queue)))
    // && (forall l: Loc :: {Between(next(queue), head, l, null)} known(l) ==>
    //     (Between(next(queue), head, l, null) <==> l == null || dom(queue)[l]))
    && tail != null
    && known(head) && known(tail) && known(null) && knownF(next(queue))
}


// ---------- Primitives for manipulating ghost state

procedure {:inline 2} TransferToqueue(t: Loc, oldVal: Loc,
    newVal: Loc, l_in:Heap)
  returns (r: bool, l_out:Heap)
  modifies queue;
{
  assert dom(l_in)[newVal];
  if (next(queue)[t] == oldVal) {
    assert knownF(next(queue));
    queue := Add(queue, t, newVal);
    assert known(head) && known(tail) && known(t) && known(oldVal) && known(newVal)
     && known(next(l_in)[newVal]) && knownF(next(queue));
    l_out := EmptyHeap();
    queue := Add(queue, newVal, next(l_in)[newVal]);
    assert knownF(next(queue));
    r := true;
  } else {
    l_out := l_in;
    r := false;
  }
}

procedure {:inline 2} TransferFromqueue(oldVal: Loc, newVal: Loc) returns (r: bool)
  modifies head, Used, queue;
{
  if (oldVal == head) {
    head := newVal;
    Used[oldVal] := true;
    queue := Remove(queue, oldVal);
    assert known(oldVal) && known(head) && knownF(next(queue));
    r := true;
  }
  else {
    r := false;
  }
}


// ---------- queue methods:

procedure test1(x: Loc, t: Loc, tn: Loc, t_Heap: Heap, x_Heap: Heap)
  requires Inv(queue, head, tail);
  requires dom(x_Heap)[x] && next(x_Heap)[x] == null;
  requires known(x) && known(t) && known(tn) && knownF(next(queue)) && knownF(next(t_Heap));
  requires dom(t_Heap) == dom(x_Heap);
  requires next(t_Heap)[x] == null;
  requires t != null && (Between(next(queue), head, t, null)
      || Used[t]);
  requires next(queue)[t] == null ==> t == tail;

  ensures {:expand} Inv(queue, head, tail);
  modifies queue;
{
  var g: bool;
  var out_heap: Heap;
  assume tn == null;
  call g, out_heap := TransferToqueue(t, tn, x, t_Heap);
  if (!g) {
    assume false;
  } else {
  assert known(head) && known(tail) && known(null) && knownF(next(queue));
  assert Between(next(queue), head, head, null);
  assert Between(next(queue), head, tail, null);
  assert Equal(BetweenSet(next(queue), head, null),
             Union(Singleton(null), dom(queue)));
  }
}

procedure test(x: Loc, x_Heap: Heap, c: Loc)
  requires Inv(queue, head, tail);
  requires dom(x_Heap)[x] && next(x_Heap)[x] == null;
  requires !Between(next(queue), head, x, null); // From linearity
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

  assert known(head) && known(tail) && known(c) && known(x) && known(null)
    && knownF(next(queue)) && knownF(next(x_Heap));

  // call g, t_Heap := TransferToqueue(tail, null, x, x_Heap);
  if (next(queue)[tail] == null) {
    queue := Add(queue, tail, x);

    assert known(head) && known(tail) && known(c) && known(x) && known(null)
      && knownF(next(queue)) && knownF(next(x_Heap));

    assert Between(next(queue), head, tail, tail) && next(queue)[tail] == x;
    assert Between(next(queue), tail, x, x);
    assert Between(next(queue), head, tail, x);

    queue := Add(queue, x, next(x_Heap)[x]);

    assert known(head) && known(tail) && known(c) && known(x) && known(null)
      && knownF(next(queue)) && knownF(next(x_Heap));
  }
}
