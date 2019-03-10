// ----------------------------------------
// Reachability axioms from Grasshopper.
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
axiom(forall S:[Ref]bool, T:[Ref]bool :: {Subset(S,T)} Subset(S,T) || (exists x:Ref :: known(x) && S[x] && !T[x]));


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

// read null  // TODO UNSOUND!! Instead, manually assume this for initial fields
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
axiom(forall f: [Ref]Ref, x: Ref, y: Ref :: {knownF(f), known(x), known(y)} Btwn(f, x, y, x) ==> x == y);

// order1
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} Btwn(f, x, y, y) && Btwn(f, x, z, z) ==> Btwn(f, x, y, z) || Btwn(f, x, z, y));

// order2
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} Btwn(f, x, y, z) ==> Btwn(f, x, y, y) && Btwn(f, y, z, z));

// transitive1
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} Btwn(f, x, y, y) && Btwn(f, y, z, z) ==> Btwn(f, x, z, z));

// transitive2
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, w: Ref :: {knownF(f), known(x), known(y), known(z), known(w)} Btwn(f, x, y, z) && Btwn(f, y, w, z) ==> Btwn(f, x, y, w) && Btwn(f, x, w, z));

// transitive3
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, w: Ref :: {knownF(f), known(x), known(y), known(z), known(w)} Btwn(f, x, y, z) && Btwn(f, x, w, y) ==> Btwn(f, x, w, z) && Btwn(f, w, y, z));

// relation between ReachW and Btwn
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} ReachW(f, x, y, z) <==> (Btwn(f, x, y, z) || (Btwn(f, x, y, y) && !Btwn(f, x, z, z))));
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} Btwn(f, x, y, z) <==> (ReachW(f, x, y, z) && ReachW(f, x, z, z)));

// btwn_write: grasshopper's update axiom
axiom (forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, u: Ref, v: Ref :: {f[u := v], known(x), known(y), known(z)}
        u != null ==>
          (Btwn(f[u := v], x, y, z) <==>
          (Btwn(f, x, y, z) && ReachW(f, x, z, u))
          || (u != z && ReachW(f, x, u, z) && ReachW(f, v, z, u)
            && (Btwn(f, x, y, u) || Btwn(f, v, y, z)))));


// ---------- Shared state and invariant

var queue: Heap;
var Used: [Ref]bool;

var head: Ref;
var tail: Ref;


function {:inline} Inv(queue: Heap, head: Ref, tail: Ref) : (bool)
{
  Btwn(next(queue), head, head, null)
    && Btwn(next(queue), head, tail, null)
    && Equal(BtwnSet(next(queue), head, null),
             Union(Singleton(null), dom(queue)))
    // && (forall l: Ref :: {Btwn(next(queue), head, l, null)} known(l) ==>
    //     (Btwn(next(queue), head, l, null) <==> l == null || dom(queue)[l]))
    && tail != null
    && known(head) && known(tail) && known(null) && knownF(next(queue))
}


// ---------- Primitives for manipulating ghost state

procedure {:inline 2} TransferToqueue(t: Ref, oldVal: Ref,
    newVal: Ref, l_in:Heap)
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

procedure {:inline 2} TransferFromqueue(oldVal: Ref, newVal: Ref) returns (r: bool)
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

procedure test1(x: Ref, t: Ref, tn: Ref, t_Heap: Heap, x_Heap: Heap)
  requires Inv(queue, head, tail);
  requires dom(x_Heap)[x] && next(x_Heap)[x] == null;
  requires known(x) && known(t) && known(tn) && knownF(next(queue)) && knownF(next(t_Heap));
  requires dom(t_Heap) == dom(x_Heap);
  requires next(t_Heap)[x] == null;
  requires t != null && (Btwn(next(queue), head, t, null)
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
  assert Btwn(next(queue), head, head, null);
  assert Btwn(next(queue), head, tail, null);
  assert Equal(BtwnSet(next(queue), head, null),
             Union(Singleton(null), dom(queue)));
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

  assert known(head) && known(tail) && known(c) && known(x) && known(null)
    && knownF(next(queue)) && knownF(next(x_Heap));

  // call g, t_Heap := TransferToqueue(tail, null, x, x_Heap);
  if (next(queue)[tail] == null) {
    queue := Add(queue, tail, x);

    assert known(head) && known(tail) && known(c) && known(x) && known(null)
      && knownF(next(queue)) && knownF(next(x_Heap));

    assert Btwn(next(queue), head, tail, tail) && next(queue)[tail] == x;
    assert Btwn(next(queue), tail, x, x);
    assert Btwn(next(queue), head, tail, x);

    queue := Add(queue, x, next(x_Heap)[x]);

    assert known(head) && known(tail) && known(c) && known(x) && known(null)
      && knownF(next(queue)) && knownF(next(x_Heap));
  }
}
