type Ref;
const null: Ref;

type Heap;
function {:linear "Node"} dom(Heap): [Ref]bool;
function next(Heap): [Ref]Ref;
function data(Heap): [Ref]int;
function {:builtin "MapConst"} MapConstLocBool(bool) : [Ref]bool;

function EmptyLmap(): (Heap);
axiom (dom(EmptyLmap()) == MapConstLocBool(false));

function Add(h: Heap, l: Ref, v: Ref): (Heap);
axiom (forall h: Heap, l: Ref, v: Ref :: dom(Add(h, l, v)) == dom(h)[l:=true] && next(Add(h, l, v)) == next(h)[l := v]);

function Remove(h: Heap, l: Ref): (Heap);
axiom (forall h: Heap, l: Ref :: dom(Remove(h, l)) == dom(h)[l:=false] && next(Remove(h, l)) == next(h));


// Concrete state of implementation
var heap: Heap;
var head: Ref;
var tail: Ref;


// The invariants
function {:inline} Inv(heap: Heap, head: Ref, tail: Ref) : bool
{
  BtwnSet(next(heap), head, null)[head] && BtwnSet(next(heap), head, null)[tail]
    && (forall l: Ref :: {known(l)} known(l) ==> (Btwn(next(heap), head, l, null) ==> l == null || dom(heap)[l]))
    //    && Subset(BtwnSet(next(heap), head, null), Union(Singleton(null), dom(heap)))
    && tail != null
    && known(head) && known(tail) && known(null) && knownF(next(heap))
}

// ---------- Primitives/helpers for modifying global state


procedure alloc(x: Ref)
  requires !dom(heap)[x] && x != null;
  ensures heap == Add(old(heap), x, null);
  ensures knownF(next(heap));
  modifies heap;
{
  assert !dom(heap)[x];
  heap := Add(heap, x, null);
}

procedure {:inline 1} read_tail() returns (t: Ref)
{
  t := tail;
}

procedure {:inline 1} read_head() returns (h: Ref)
{
  h := head;
}

procedure {:inline 1} read_next(x: Ref) returns (y: Ref)
  requires dom(heap)[x];
  ensures known(y);
{
  y := next(heap)[x];
}

procedure cas_next(x, x_old, x_new: Ref)
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

procedure cas_tail(t_old, t_new: Ref)
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

procedure cas_head(h_old, h_new: Ref)
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


procedure offer(v: int, x: Ref)
  returns (res: bool)
  requires Inv(heap, head, tail);
  ensures Inv(heap, head, tail);
  modifies heap, tail;
{
  var t, tn: Ref;
  var b: bool;
  assume !Btwn(next(heap), head, x, null) && !dom(heap)[x];

  assert known(x);
  call alloc(x);

  while (true)
    invariant Inv(heap, head, tail);
    invariant known(x) && x != null && dom(heap)[x] && next(heap)[x] == null;
    invariant !Btwn(next(heap), head, x, null);
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
  var h, h1, t, x: Ref;
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
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} BtwnSet(f, x, z)[y] <==> Btwn(f, x, y, z));
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} Btwn(f, x, y, z) ==> BtwnSet(f, x, z)[y]);
axiom(forall f: [Ref]Ref, x: Ref :: {knownF(f), known(x)} Btwn(f, x, x, x));
axiom(forall f: [Ref]Ref, x: Ref, z: Ref :: {BtwnSet(f, x, z)} Btwn(f, z, z, z));


//////////////////////////
// Axioms for Btwn
//////////////////////////

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

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.
// It cannot be proved using the rest of the axioms.
axiom(forall f: [Ref]Ref, u:Ref, x: Ref :: {knownF(f), known(x), known(u)} Btwn(f, u, x, x) ==> Btwn(f, u, u, x));

// relation between ReachW and Btwn
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} ReachW(f, x, y, z) <==> (Btwn(f, x, y, z) || (Btwn(f, x, y, y) && !Btwn(f, x, z, z))));
axiom(forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref :: {knownF(f), known(x), known(y), known(z)} Btwn(f, x, y, z) <==> (ReachW(f, x, y, z) && ReachW(f, x, z, z)));

// BWr: grasshopper's update axiom
axiom (forall f: [Ref]Ref, x: Ref, y: Ref, z: Ref, u: Ref, v: Ref :: {f[u := v], known(x), known(y), known(z)}
        Btwn(f[u := v], x, y, z) <==>
          (Btwn(f, x, y, z) && ReachW(f, x, z, u))
          || (u != z && ReachW(f, x, u, z) && ReachW(f, v, z, u)
            && (Btwn(f, x, y, u) || Btwn(f, v, y, z))));


/* Not sure if this is the same update as the grasshopper axiom BWr above:
// update
axiom(forall f: [Ref]Ref, u: Ref, v: Ref, x: Ref, p: Ref, q: Ref :: {knownF(f), known(x), known(u), known(v), known(p), known(q)} ReachW(f[p := q], u, v, x) <==> ((ReachW(f, u, v, p) && ReachW(f, u, v, x)) || (ReachW(f, u, p, x) && p != x && ReachW(f, q, v, p) && ReachW(f, q, v, x))));
*/

/* Why are these needed?
axiom (forall f: [Ref]Ref, p: Ref, q: Ref, u: Ref, w: Ref :: {knownF(f), known(p), known(q), known(u), known(w)} ReachW(f, u, w, p) ==> Equal(BtwnSet(f[p := q], u, w), BtwnSet(f, u, w)));
axiom (forall f: [Ref]Ref, p: Ref, q: Ref, u: Ref, w: Ref :: {knownF(f), known(p), known(q), known(u), known(w)} p != w && ReachW(f, u, p, w) && ReachW(f, q, w, p) ==> Equal(BtwnSet(f[p := q], u, w), Union(BtwnSet(f, u, p), BtwnSet(f, q, w))));
axiom (forall f: [Ref]Ref, p: Ref, q: Ref, u: Ref, w: Ref :: {knownF(f), known(p), known(q), known(u), known(w)} ReachW(f, u, w, p) || (p != w && ReachW(f, u, p, w) && ReachW(f, q, w, p)) || Equal(BtwnSet(f[p := q], u, w), Empty()));
 */
