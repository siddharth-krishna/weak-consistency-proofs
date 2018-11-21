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
    && (forall l: Loc :: known(l) ==> (Between(next(heap), head, l, null) ==> l == null || dom(heap)[l]))
    //    && Subset(BetweenSet(next(heap), head, null), Union(Singleton(null), dom(heap)))
    && tail != null
    && known(head) && known(tail) && known(null) && knownF(next(heap))
}

// ---------- Primitives/helpers for modifying global state


procedure alloc(x: Loc)
  requires !dom(heap)[x] && x != null;
  ensures heap == Add(old(heap), x, null);
  ensures knownF(next(heap));
  modifies heap;
{
  assert !dom(heap)[x];
  heap := Add(heap, x, null);
}

procedure {:inline 1} read_tail() returns (t: Loc)
{
  t := tail;
}

procedure {:inline 1} read_head() returns (h: Loc)
{
  h := head;
}

procedure {:inline 1} read_next(x: Loc) returns (y: Loc)
  ensures known(y);
{
  y := next(heap)[x];
}

procedure cas_next(x, x_old, x_new: Loc)
  returns (res: bool)
  requires dom(heap)[x];
  ensures next(old(heap))[x] == x_old ==> res && heap == Add(old(heap), x, x_new);
  ensures next(old(heap))[x] != x_old ==> !res && heap == old(heap);
  ensures knownF(next(heap));
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

procedure cas_tail(t_old, t_new: Loc)
  returns (res: bool)
  ensures old(tail) == t_old ==> res && tail == t_new;
  ensures old(tail) != t_old ==> !res && tail == old(tail);
  modifies tail;
{
  if (tail == t_old) {
    tail := t_new;
    res := true;
  } else {
    res := false;
  }
}

procedure cas_head(h_old, h_new: Loc)
  returns (res: bool)
  ensures old(head) == h_old ==> res && head == h_new;
  ensures old(head) != h_old ==> !res && head == old(head);
  modifies head;
{
  if (head == h_old) {
    head := h_new;
    res := true;
  } else {
    res := false;
  }
}


// ---------- The ADT methods


procedure offer(v: int, x: Loc)
  returns (res: bool)
  requires Inv(heap, head, tail);
  ensures Inv(heap, head, tail);
  modifies heap, tail;
{
  var t, tn: Loc;
  var b: bool;
  assume !Between(next(heap), head, x, null) && !dom(heap)[x];

  assert known(x);
  assert Inv(heap, head, tail);
  call alloc(x);
  assert Inv(heap, head, tail);

  while (true)
    invariant Inv(heap, head, tail);
    invariant known(x) && x != null && dom(heap)[x] && next(heap)[x] == null;
    invariant !Between(next(heap), head, x, null);
  {
    call t := read_tail();
    assert Inv(heap, head, tail);

    call tn := read_next(t);

    if (tn == null) {
      assert Inv(heap, head, tail);
      call b := cas_next(t, tn, x);
      if (b) {
        // TODO prove that abstract state now has v in it
        res := true;

        assert Inv(heap, head, tail);
        return;
      }
    } else {
      call b:= cas_tail(t, tn);

      assert Inv(heap, head, tail);
    }
  }
}

procedure poll()
  returns (v: int)
  requires Inv(heap, head, tail);
  ensures Inv(heap, head, tail);
  modifies heap, head, tail;
{
  var h, h1, t, x: Loc;
  var b: bool;

  while (true)
    invariant Inv(heap, head, tail);
  {
    call h := read_head();
    call t := read_tail();
    call x := read_next(h);

    call h1 := read_head();
    if (h == h1) {  // TODO is this really necessary?
      if (h == t) {
        if (x == null) {
          return; // Queue is empty
        }
        call b := cas_tail(t, x);
      } else {
        // TODO return value in x
        call b := cas_head(h, x);
        if (b) {
          return;
        }
      }
    }
  }
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
// Between set constructor
//////////////////////////
function BetweenSet(f: [Loc]Loc, x: Loc, z: Loc) returns ([Loc]bool);

////////////////////////////////////////////////////
// axioms relating Between and BetweenSet
////////////////////////////////////////////////////
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {knownF(f), known(x), known(y), known(z)} BetweenSet(f, x, z)[y] <==> Between(f, x, y, z));
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {knownF(f), known(x), known(y), known(z)} Between(f, x, y, z) ==> BetweenSet(f, x, z)[y]);
axiom(forall f: [Loc]Loc, x: Loc :: {knownF(f), known(x)} Between(f, x, x, x));
axiom(forall f: [Loc]Loc, x: Loc, z: Loc :: {BetweenSet(f, x, z)} Between(f, z, z, z));


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

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.
// It cannot be proved using the rest of the axioms.
axiom(forall f: [Loc]Loc, u:Loc, x: Loc :: {knownF(f), known(x), known(u)} Between(f, u, x, x) ==> Between(f, u, u, x));

// relation between Avoiding and Between
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {knownF(f), known(x), known(y), known(z)} Avoiding(f, x, y, z) <==> (Between(f, x, y, z) || (Between(f, x, y, y) && !Between(f, x, z, z))));
axiom(forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc :: {knownF(f), known(x), known(y), known(z)} Between(f, x, y, z) <==> (Avoiding(f, x, y, z) && Avoiding(f, x, z, z)));

// BWr: grasshopper's update axiom
axiom (forall f: [Loc]Loc, x: Loc, y: Loc, z: Loc, u: Loc, v: Loc :: {f[u := v], known(x), known(y), known(z)}
        Between(f[u := v], x, y, z) <==>
          (Between(f, x, y, z) && Avoiding(f, x, z, u))
          || (u != z && Avoiding(f, x, u, z) && Avoiding(f, v, z, u)
            && (Between(f, x, y, u) || Between(f, v, y, z))));


/* Not sure if this is the same update as the grasshopper axiom BWr above:
// update
axiom(forall f: [Loc]Loc, u: Loc, v: Loc, x: Loc, p: Loc, q: Loc :: {knownF(f), known(x), known(u), known(v), known(p), known(q)} Avoiding(f[p := q], u, v, x) <==> ((Avoiding(f, u, v, p) && Avoiding(f, u, v, x)) || (Avoiding(f, u, p, x) && p != x && Avoiding(f, q, v, p) && Avoiding(f, q, v, x))));
*/

/* Why are these needed?
axiom (forall f: [Loc]Loc, p: Loc, q: Loc, u: Loc, w: Loc :: {knownF(f), known(p), known(q), known(u), known(w)} Avoiding(f, u, w, p) ==> Equal(BetweenSet(f[p := q], u, w), BetweenSet(f, u, w)));
axiom (forall f: [Loc]Loc, p: Loc, q: Loc, u: Loc, w: Loc :: {knownF(f), known(p), known(q), known(u), known(w)} p != w && Avoiding(f, u, p, w) && Avoiding(f, q, w, p) ==> Equal(BetweenSet(f[p := q], u, w), Union(BetweenSet(f, u, p), BetweenSet(f, q, w))));
axiom (forall f: [Loc]Loc, p: Loc, q: Loc, u: Loc, w: Loc :: {knownF(f), known(p), known(q), known(u), known(w)} Avoiding(f, u, w, p) || (p != w && Avoiding(f, u, p, w) && Avoiding(f, q, w, p)) || Equal(BetweenSet(f[p := q], u, w), Empty()));
 */
