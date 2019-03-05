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
    assert known(head) && known(tail) && known(null) && known(x1) && known(c)
      && known(next(queue)[x1])
      && knownF(next(queue));

    old_q := queue;
    queue := Add(queue, tail, x1);

    assert known(head) && known(tail) && known(null) && known(x1)
      && knownF(next(queue));

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

  assert known(head) && known(tail) && known(c) && known(x) && known(null)
    && knownF(next(queue)) && knownF(next(x_Heap));

  // call g, t_Heap := TransferToqueue(tail, null, x, x_Heap);
  if (next(queue)[tail] == null) {
    queue := Add(queue, tail, x);

    assert Between(next(queue), head, tail, next(queue)[x]);  // TODO this fails

    assert knownF(next(queue));
    queue := Add(queue, x, next(x_Heap)[x]);

    assert knownF(next(queue));
  }
}
