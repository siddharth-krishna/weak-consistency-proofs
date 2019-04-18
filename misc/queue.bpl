// ----------------------------------------
// A simple queue implementation based on the Michael-Scott queue.
// Assumes GC, so does not free dequeued nodes.
// Uses Grasshopper style heap encoding and axioms (using known terms as triggers).
// Also uses FP sets for linearity instead of Heaps and dom(heap).
//
// Use options -noinfer -typeEncoding:m -useArrayTheory
// ----------------------------------------


// ---------- Types of methods and invocations

type Method;

type Invoc;

// Boilerplate stuff for linear variables
function {:builtin "MapConst"} MapConstInvocBool(bool) : [Invoc]bool;
function {:inline} {:linear "this"} TidCollector(x: Invoc) : [Invoc]bool
{
  MapConstInvocBool(false)[x := true]
}


// ---------- Types and axiomatization of sequences (of invocations)

// Sequences of invocations
type SeqInvoc;

function Seq_append(s: SeqInvoc, o: Invoc) returns (t: SeqInvoc);

function Seq_elem(n: Invoc, s: SeqInvoc) : bool;

// Relationship between elem and append
// axiom (forall n1, n2: Invoc, s: SeqInvoc :: {Seq_elem(n1, Seq_append(s, n2))}
//        Seq_elem(n1, s) ==> Seq_elem(n1, Seq_append(s, n2)));
axiom (forall n1, n2: Invoc, s: SeqInvoc :: {Seq_elem(n1, Seq_append(s, n2))}
       Seq_elem(n1, Seq_append(s, n2)) <==> Seq_elem(n1, s) || n1 == n2);

// axiom (forall n: Invoc, s: SeqInvoc :: {Seq_elem(n, Seq_append(s, n))}
//        Seq_elem(n, Seq_append(s, n)));


// ---------- Types and axiomatization of sets (of invocations)

// Sets of invocations
type SetInvoc;

const Set_empty: SetInvoc;

function Set(n: Invoc) : SetInvoc;  // singleton set

function Set_elem(n: Invoc, s: SetInvoc) : bool;

function Set_subset(s: SetInvoc, t: SetInvoc) : bool;

function Set_equal(s, t: SetInvoc) : bool;  // helper function to prove sets are equal

// extensionality
axiom (forall s, t: SetInvoc :: {Set_equal(s, t)}
  (forall n: Invoc :: Set_elem(n, s) <==> Set_elem(n, t)) ==> Set_equal(s, t) && s == t);

// Set_empty is a subset of anything
axiom (forall s: SetInvoc :: Set_subset(Set_empty, s));

// Nothing is an elem of Set_empty
axiom (forall n: Invoc :: !Set_elem(n, Set_empty));

// Set(n) definition
axiom (forall n1, n2: Invoc :: {Set_elem(n2, Set(n1))}
  Set_elem(n2, Set(n1)) <==> n2 == n1);

// subset is reflexive
axiom (forall s: SetInvoc :: Set_subset(s, s));

// subset is transitive
axiom (forall s, t, u: SetInvoc ::
    {Set_subset(s, t), Set_subset(t, u), Set_subset(s, u)}
  Set_subset(s, t) && Set_subset(t, u) ==> Set_subset(s, u));

// definition of subset in terms of elem
axiom (forall s, t: SetInvoc :: (forall n: Invoc :: Set_elem(n, s) ==> Set_elem(n, t)) ==> Set_subset(s, t));

function Set_union(s1: SetInvoc, s2: SetInvoc) returns (t: SetInvoc);

// union is idempotent
axiom (forall s: SetInvoc :: s == Set_union(s, s));

// union is associative
axiom (forall s, t: SetInvoc :: {Set_union(s, t), Set_union(t, s)}
  Set_union(s, t) == Set_union(t, s));

// union preserves subset
axiom (forall s1, s2, s3: SetInvoc :: {Set_subset(s1, s2), Set_subset(s1, Set_union(s2, s3))}
  Set_subset(s1, s2) ==> Set_subset(s1, Set_union(s2, s3)));

// union with empty
axiom (forall s: SetInvoc :: Set_union(s, Set_empty) == s);
axiom (forall s: SetInvoc :: Set_union(Set_empty, s) == s);

// union is monotonic w.r.t subset
// axiom (forall s, t1, t2: SetInvoc ::
//   Set_subset(t1, t2) ==> Set_subset(Set_union(s, t1), Set_union(s, t2)));

// axiom (forall s, t1, t2: SetInvoc ::
//   Set_subset(t1, s) && Set_subset(t2, s) ==> Set_subset(Set_union(t1, t2), s));

// relation between union and elem
axiom (forall n: Invoc, s, t: SetInvoc ::
    {Set_elem(n, Set_union(s, t)), Set_elem(n, t)}
    {Set_elem(n, Set_union(s, t)), Set_elem(n, s)}
  Set_elem(n, Set_union(s, t)) <==> Set_elem(n, s) || Set_elem(n, t));

// intersection
function Set_inter(s1: SetInvoc, s2: SetInvoc) returns (t: SetInvoc);

// relation between intersection and elem
axiom (forall n: Invoc, s, t: SetInvoc ::
    {Set_elem(n, Set_inter(s, t)), Set_elem(n, t)}
    {Set_elem(n, Set_inter(s, t)), Set_elem(n, s)}
  Set_elem(n, Set_inter(s, t)) <==> Set_elem(n, s) && Set_elem(n, t));

// intersection with empty
axiom (forall s: SetInvoc :: Set_inter(s, Set_empty) == Set_empty);
axiom (forall s: SetInvoc :: Set_inter(Set_empty, s) == Set_empty);

function Set_ofSeq(q: SeqInvoc) returns (s: SetInvoc);

function Set_add(s: SetInvoc, n: Invoc) returns (t: SetInvoc);

// add in terms of union and singleton
axiom (forall s: SetInvoc, n: Invoc :: {Set_union(s, Set(n))} Set_add(s, n) == Set_union(s, Set(n)));

// Relation between add and elem
axiom (forall s: SetInvoc, n1, n2: Invoc :: {Set_elem(n1, Set_add(s, n2))}
  Set_elem(n1, Set_add(s, n2)) <==> n1 == n2 || Set_elem(n1, s));
axiom (forall s: SetInvoc, n: Invoc :: {Set_elem(n, s), Set_add(s, n)}
  Set_elem(n, s) ==> Set_add(s, n) == s);

// What happens when you add to empty
axiom (forall n: Invoc :: {Set_add(Set_empty, n)} Set_add(Set_empty, n) == Set(n));

// Relation between union and elem
// axiom (forall s, t: SetInvoc, n1: Invoc :: Set_elem(n1, Set_union(s, t))
//        ==> Set_elem(n1, s) || Set_elem(n1, t));

// add preserves subset relation
// axiom (forall s, t: SetInvoc, n: Invoc :: Set_subset(s, t) ==> Set_subset(Set_add(s, n), Set_add(t, n)));
axiom (forall s, t: SetInvoc, n: Invoc :: {Set_subset(s, Set_add(t, n))}
  Set_subset(s, t) ==> Set_subset(s, Set_add(t, n)));

// Relation between Set_ofSeq, add, and append
axiom (forall q: SeqInvoc, n: Invoc :: {Set_ofSeq(Seq_append(q, n))}
  Set_ofSeq(Seq_append(q, n)) == Set_add(Set_ofSeq(q), n));

// Relation between Set_ofSeq, Set_elem, and Seq_elem
axiom (forall q: SeqInvoc, n: Invoc :: {Set_elem(n, Set_ofSeq(q))}
  Seq_elem(n, q) <==> Set_elem(n, Set_ofSeq(q)));


// Distinct sequences
function Seq_distinct(q: SeqInvoc) : bool;

axiom (forall q: SeqInvoc, n: Invoc :: {Seq_distinct(Seq_append(q, n))}
  Seq_distinct(q) && !Seq_elem(n, q) ==> Seq_distinct(Seq_append(q, n)));


// Seq_restr(q, s) = sequence obtained by restricting q to s
function Seq_restr(q: SeqInvoc, s: SetInvoc) : SeqInvoc;

// The identity restriction
axiom (forall q: SeqInvoc :: {Seq_restr(q, Set_ofSeq(q))}
  Seq_restr(q, Set_ofSeq(q)) == q);

// Effect of appending new element on restriction
axiom (forall q: SeqInvoc, s: SetInvoc, n: Invoc :: {Seq_restr(Seq_append(q, n), s)}
  Seq_distinct(Seq_append(q, n)) && Set_subset(s, Set_ofSeq(q))
  ==> Seq_restr(Seq_append(q, n), s) == Seq_restr(q, s));

// Relation between Seq_elem and Seq_restr
axiom (forall q: SeqInvoc, s: SetInvoc, n: Invoc :: {Seq_elem(n, Seq_restr(q, s))}
  Seq_elem(n, Seq_restr(q, s)) <==> Seq_elem(n, q) && Set_elem(n, s));


// Implicit (strict) order of a sequence
function Seq_ord(q: SeqInvoc, n1, n2: Invoc) : bool;

// This order is transitive
// axiom (forall q: SeqInvoc, n1, n2, n3: Invoc :: //{}
//   Seq_ord(q, n1, n2) && Seq_ord(q, n2, n3) ==> Seq_ord(q, n1, n3));

// Adding to the restriction set is append if ordered correctly
axiom (forall q: SeqInvoc, s: SetInvoc, n: Invoc :: {Seq_restr(q, Set_add(s, n))}
  (forall n1: Invoc :: Seq_elem(n1, Seq_restr(q, s)) ==> Seq_ord(q, n1, n))
  && Seq_elem(n, q) && !Set_elem(n, s)
  ==> Seq_restr(q, Set_add(s, n)) == Seq_append(Seq_restr(q, s), n));

// Appending extends order
axiom (forall q: SeqInvoc, n, n1, n2: Invoc :: {Seq_ord(Seq_append(q, n), n1, n2)}
  Seq_distinct(q) ==>
  (Seq_ord(Seq_append(q, n), n1, n2)
    <==> (Seq_elem(n1, q) && Seq_elem(n2, q) && Seq_ord(q, n1, n2))
      || (Seq_elem(n1, q) && n2 == n)));


// ---------- Axioms of the queue ADT

const unique Queue.push, Queue.pop, Queue.size: Method;

function invoc_m(n: Invoc) : Method;
function invoc_k(n: Invoc) : Key;

type Queue.State;

function Queue.stateArray(s: Queue.State) : [int]Key;
function Queue.stateHead(s: Queue.State) : int;
function Queue.stateTail(s: Queue.State) : int;

function Queue.ofSeq(s: SeqInvoc) : Queue.State;

// Effect of pop to the abstract state of a Queue
axiom (forall s: SeqInvoc, n: Invoc :: {Queue.ofSeq(Seq_append(s, n))}
  invoc_m(n) == Queue.pop
  ==> ((Queue.stateHead(Queue.ofSeq(s)) != Queue.stateTail(Queue.ofSeq(s))
      && Queue.stateHead(Queue.ofSeq(Seq_append(s, n)))
      == Queue.stateHead(Queue.ofSeq(s)) + 1)
    || (Queue.stateHead(Queue.ofSeq(s)) == Queue.stateTail(Queue.ofSeq(s))
      && Queue.stateHead(Queue.ofSeq(Seq_append(s, n)))
      == Queue.stateHead(Queue.ofSeq(s))))
  && Queue.stateTail(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateTail(Queue.ofSeq(s))
  && Queue.stateArray(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateArray(Queue.ofSeq(s)));

// Effect of push to the abstract state of a Queue
axiom (forall s: SeqInvoc, n: Invoc :: {Queue.ofSeq(Seq_append(s, n))}
  invoc_m(n) == Queue.push
  ==> Queue.stateHead(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateHead(Queue.ofSeq(s))
  && Queue.stateTail(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateTail(Queue.ofSeq(s)) + 1
  && Queue.stateArray(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateArray(Queue.ofSeq(s))[
      Queue.stateTail(Queue.ofSeq(s)) := invoc_k(n)]);

// Effect of size to the abstract state of a Queue
axiom (forall s: SeqInvoc, n: Invoc :: {Queue.ofSeq(Seq_append(s, n))}
  invoc_m(n) == Queue.size
  ==> Queue.stateHead(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateHead(Queue.ofSeq(s))
  && Queue.stateTail(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateTail(Queue.ofSeq(s))
  && Queue.stateArray(Queue.ofSeq(Seq_append(s, n)))
    == Queue.stateArray(Queue.ofSeq(s)));


// ---------- Representation of execution and linearization

// hb(x, y) : x happens-before y.
// We assume there exists such a function, given by the client program
function hb(x: Invoc, y: Invoc) : bool;
axiom (forall n: Invoc :: !hb(n, n));

// A shared global variable that builds the linearization
var {:layer 1,2} lin: SeqInvoc;

// A map from invocations to the set of prior invocations visible to them
var {:layer 1,2} vis: [Invoc]SetInvoc;

// The set of invocations that have been called
var {:layer 0,1} called: [Invoc]bool;

// The set of invocations that have returned
var {:layer 0,1} returned: [Invoc]bool;


// ---------- Heap representation and linearity


type Ref;
const null: Ref;

function {:builtin "MapConst"} MapConstBool(bool) : [Ref]bool;

const emptySet : [Ref]bool;
axiom (emptySet == MapConstBool(false));

// Linearity stuff:

function {:inline} {:linear "FP"} FPCollector(x: [Ref]bool) : [Ref]bool { x }


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

type Key;

// Fields:
var {:layer 0, 1} next: [Ref]Ref;
var {:layer 0, 1} data: [Ref]Key;

var {:linear "FP"} {:layer 0, 1} queueFP: [Ref]bool;  // TODO make layer 1,1 and intro actions to modify?
var {:linear "FP"} {:layer 0, 1} usedFP: [Ref]bool;

var {:layer 0, 1} head: Ref;
var {:layer 0, 1} tail: Ref;
var {:layer 0, 1} start: Ref; // The first head. To define usedFP

// Tags storing write operations:
var {:layer 0, 1} nextTags: [Ref]SetInvoc;
var {:layer 0, 1} dataTags: [Ref]SetInvoc;
var {:layer 0, 1} headTags: SetInvoc;
var {:layer 0, 1} tailTags: SetInvoc;

// Witness to prove that nextTags contains singleton sets
var {:layer 1, 1} nextInvoc: [Ref]Invoc;
// Witness for node that contains invoc in nextTags
var {:layer 1, 1} nextRef: [Invoc]Ref;


// Abstract state
var {:layer 1,1} absRefs: [int]Ref;  // connection between abstract and concrete


function {:inline} Inv(queueFP: [Ref]bool, usedFP: [Ref]bool, start: Ref,
    head: Ref, tail: Ref, next: [Ref]Ref, data: [Ref]Key,
    nextTags: [Ref]SetInvoc, nextInvoc: [Ref]Invoc, nextRef: [Invoc]Ref,
    lin: SeqInvoc, vis: [Invoc]SetInvoc, absRefs: [int]Ref,
    called: [Invoc]bool, returned: [Invoc]bool) : bool
{
  // There is a list from head to null
  Btwn(next, head, head, null)
  && (forall x: Ref :: {queueFP[x]}{Btwn(next, head, x, null)}
    known(x) ==> (queueFP[x] <==> (Btwn(next, head, x, null) && x != null)))
  // Tail is on that list
  && Btwn(next, head, tail, null) && tail != null
  // There is also a list from start to head // TODO try just lseg(c, head)
  && Btwn(next, start, start, head)
  && (forall x: Ref :: {usedFP[x]}{Btwn(next, start, x, head)}
    known(x) ==> (usedFP[x] <==> (Btwn(next, start, x, head) && x != head)))
  // Terms needed for axiom triggers
  && known(start) && known(head) && known(tail) && known(null) && knownF(next)
  // Relate abstract state to concrete state:
  && (forall i: int :: {absRefs[i]}
    i < -1 || Queue.stateTail(Queue.ofSeq(lin)) <= i <==> absRefs[i] == null)
  && absRefs[Queue.stateHead(Queue.ofSeq(lin)) - 1] == head
  && (forall i: int :: {next[absRefs[i]]}
    -1 <= i && i < Queue.stateTail(Queue.ofSeq(lin))
    ==> absRefs[i + 1] == next[absRefs[i]])
  && (forall i, j: int :: {absRefs[i], absRefs[j]}
    absRefs[i] == absRefs[j] && absRefs[i] != null ==> i == j)
  && (forall i: int :: {Queue.stateArray(Queue.ofSeq(lin))[i], data[absRefs[i]]}
    0 <= i && i < Queue.stateTail(Queue.ofSeq(lin))
    ==> Queue.stateArray(Queue.ofSeq(lin))[i] == data[absRefs[i]])
  && (forall y: Ref :: {Btwn(next, head, y, null), next[y]} known(y) ==>
    (Btwn(next, head, y, null) && y != null && next[y] == null
    ==> y == absRefs[Queue.stateTail(Queue.ofSeq(lin)) - 1]))
  // nextTags only contains singleton sets of push operations
  && (forall y: Ref :: {known(y)} known(y) ==>  // TODO trigger?
    (Btwn(next, start, y, null) && y != null && next[y] != null
    ==> nextTags[y] == Set(nextInvoc[y]) && invoc_m(nextInvoc[y]) == Queue.push))
  && nextTags[absRefs[Queue.stateTail(Queue.ofSeq(lin)) - 1]] == Set_empty
  // lin is made up of nextInvoc[y] for y in the queue
  && (forall n: Invoc :: {Seq_elem(n, lin)} known(nextRef[n]) && invoc_m(n) == Queue.push ==>
    (Seq_elem(n, lin) 
      <==> Btwn(next, start, nextRef[n], null)
        && nextRef[n] != null && next[nextRef[n]] != null))
  // lin is ordered by order of nodes in queue
  && (forall n1, n2: Invoc :: {Seq_ord(lin, n1, n2)}
    known(nextRef[n1]) && known(nextRef[n2]) ==>
    (invoc_m(n1) == Queue.push && invoc_m(n2) == Queue.push
    && Seq_elem(n1, lin) && Seq_elem(n2, lin)
    ==> (Seq_ord(lin, n1, n2)
      <==> Btwn(next, nextRef[n1], nextRef[n1], nextRef[n2]) && nextRef[n1] != nextRef[n2])))
  // Default value for nextRef is null
  && (forall n: Invoc :: {nextRef[n]}
    !Seq_elem(n, lin) || invoc_m(n) != Queue.push ==> nextRef[n] == null)
  // nextRef is injective (for pushes in lin)
  && (forall n1, n2: Invoc :: {nextRef[n1], nextRef[n2]}
    Seq_elem(n1, lin) && Seq_elem(n2, lin)
    && invoc_m(n1) == Queue.push && invoc_m(n2) == Queue.push
    && nextRef[n1] == nextRef[n2] ==> n1 == n2)
  // nextRef and nextInvoc are inverses
  // && (forall n: Invoc :: {nextInvoc[nextRef[n]]} nextInvoc[nextRef[n]] == n)
  && (forall y: Ref :: {nextRef[nextInvoc[y]]} known(y) ==>
    (Btwn(next, start, y, null) && next[y] != null ==> nextRef[nextInvoc[y]] == y))
  // lin only contains called things
  && (forall n: Invoc :: {Seq_elem(n, lin)} Seq_elem(n, lin) ==> called[n])
  && Seq_distinct(lin)
  // vis sets only contain linearized ops
  && (forall n1, n2: Invoc :: {Set_elem(n1, vis[n2])}
    Set_elem(n1, vis[n2]) && returned[n2] ==> Set_elem(n1, Set_ofSeq(lin)))
  // Used to infer that invocations don't modify vis after they've returned
  && (forall n1, n2 : Invoc :: called[n1] && hb(n2, n1) ==> returned[n2])
  // To establish precondition of intro_writeLin
  && (forall n: Invoc :: returned[n] ==> Seq_elem(n, lin))
  // Axiom of heap encoding
  && next[null] == null
}

function {:inline} preLP(called: [Invoc]bool, returned: [Invoc]bool, lin: SeqInvoc, this: Invoc) : bool
{
  called[this] && !returned[this] && !Seq_elem(this, lin)
}

function {:inline} postLP(called: [Invoc]bool, returned: [Invoc]bool, lin: SeqInvoc, this: Invoc) : bool
{
  called[this] && !returned[this] && Seq_elem(this, lin)
}


// ---------- Primitives for manipulating global state

procedure {:atomic} {:layer 1} readHead_atomic() returns (x: Ref)
{ x := head; }

procedure {:yields} {:layer 0} {:refines "readHead_atomic"} readHead() returns (x: Ref);

procedure {:atomic} {:layer 1} readTail_atomic() returns (x: Ref)
{ x := tail; }

procedure {:yields} {:layer 0} {:refines "readTail_atomic"} readTail() returns (x: Ref);

procedure {:atomic} {:layer 1} casTail_atomic(ole: Ref, new: Ref, {:linear "this"} n: Invoc)
  returns (b: bool)
  modifies tail, tailTags;
{
  if (tail == ole) {
    tail := new;
    tailTags := Set_add(tailTags, n);
    b := true;
  } else {
    b := false;
  }
}

procedure {:yields} {:layer 0} {:refines "casTail_atomic"}
  casTail(ole: Ref, new: Ref, {:linear "this"} n: Invoc) returns (b: bool);

procedure {:atomic} {:layer 1} readNext_atomic(x: Ref) returns (y: Ref)
{
  assert queueFP[x] || usedFP[x];
  y := next[x];
  assume known(y);
}

procedure {:yields} {:layer 0} {:refines "readNext_atomic"} readNext(x: Ref) returns (y: Ref);

procedure {:atomic} {:layer 1} readData_atomic(x: Ref) returns (k: Key)
{
  assert queueFP[x] || usedFP[x];
  k := data[x];
}

procedure {:yields} {:layer 0} {:refines "readData_atomic"} readData(x: Ref) returns (k: Key);

procedure {:atomic} {:layer 1} writeNext_atomic(x: Ref, y: Ref,
    {:linear "FP"} FP:[Ref]bool, {:linear "this"} n: Invoc)
  modifies next, nextTags;
{
  assert FP[x];
  next := next[x := y];
  nextTags[x] := Set_add(nextTags[x], n);
  assume knownF(next);
}

procedure {:yields} {:layer 0} {:refines "writeNext_atomic"}
  writeNext(x: Ref, y: Ref, {:linear "FP"} FP:[Ref]bool, {:linear "this"} n: Invoc);

procedure {:atomic} {:layer 1} casNextTransfer_atomic(x: Ref, oldVal: Ref,
    newVal: Ref, {:linear_in "FP"} inFP:[Ref]bool, {:linear "this"} n: Invoc)
  returns (b: bool, {:linear "FP"} outFP:[Ref]bool)
  modifies next, queueFP, nextTags;
{
  assert inFP[newVal];
  if (next[x] == oldVal) {
    next := next[x := newVal];
    nextTags[x] := Set_add(nextTags[x], n);
    outFP := emptySet;
    queueFP := queueFP[newVal := true];
    assume knownF(next);
    b := true;
  } else {
    outFP := inFP;
    b := false;
  }
}

procedure {:yields} {:layer 0} {:refines "casNextTransfer_atomic"}
  casNextTransfer(x: Ref, oldVal: Ref, newVal: Ref, {:linear_in "FP"} inFP:[Ref]bool,
    {:linear "this"} n: Invoc)
  returns (b: bool, {:linear "FP"} outFP:[Ref]bool);

procedure {:atomic} {:layer 1} casHeadTransfer_atomic(oldVal: Ref, newVal: Ref,
    {:linear "this"} n: Invoc)
  returns (b: bool)
  modifies head, usedFP, queueFP, headTags;
{
  if (oldVal == head) {
    head := newVal;
    headTags := Set_add(headTags, n);
    usedFP[oldVal] := true;
    queueFP := queueFP[oldVal := false];
    b := true;
  }
  else {
    b := false;
  }
}

procedure {:yields} {:layer 0} {:refines "casHeadTransfer_atomic"}
  casHeadTransfer(oldVal: Ref, newVal: Ref, {:linear "this"} n: Invoc) returns (b: bool);


// ---------- Primitives for manipulating logical/abstract state

procedure {:layer 1} {:inline 1} intro_writeAbsRefs(k: Key, x: Ref)
  // ensures {:layer 1} absRefs == old(absRefs)[Queue.stateTail(Queue.ofSeq(lin)) := x];
  modifies absRefs;
{
  absRefs[Queue.stateTail(Queue.ofSeq(lin))] := x;
}

procedure {:layer 1} {:inline 1} intro_getHeadIndex() returns (ci: int)
{
  ci := Queue.stateHead(Queue.ofSeq(lin));
}

// Return the tail of the concrete queue
procedure {:layer 1} {:inline 1} intro_getTail() returns (t: Ref);
  ensures {:layer 1} known(t) && t != null && next[t] == null && Btwn(next, head, t, null);

// Return the tail of the abstract queue
procedure {:layer 1} {:inline 1} intro_getTailIndex() returns (ti: int)
{
  ti := Queue.stateTail(Queue.ofSeq(lin));
}


procedure {:layer 1} {:inline 1} intro_writeNextInvoc(x: Ref, n: Invoc)
  modifies nextInvoc, nextRef;
{
  nextInvoc[x] := n;
  nextRef[n] := x;
}

procedure {:layer 1} intro_readNextTags(x: Ref, v: SetInvoc) returns (v1: SetInvoc)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  requires {:layer 1} known(x) && Btwn(next, start, x, null) && x != null;
  ensures {:layer 1} next[x] == null ==> v1 == v;
  ensures {:layer 1} next[x] != null ==> Seq_elem(nextInvoc[x], lin) && v1 == Set_add(v, nextInvoc[x]);
{
  v1 := Set_union(v, Set_inter(nextTags[x], Set_ofSeq(lin)));
  // Trigger some axioms:
  assert {:layer 1} (forall n: Invoc :: {Set_elem(n, v1)} Set_elem(n, v1)
    <==> Set_elem(n, v) || (Set_elem(n, nextTags[x]) && Set_elem(n, Set_ofSeq(lin))));
  assert {:layer 1} next[x] != null ==> Set_equal(v1, Set_add(v, nextInvoc[x]));
}

procedure {:layer 1} intro_readLin() returns (s: SetInvoc)
  ensures {:layer 1} s == Set_ofSeq(lin);
{
  s := Set_ofSeq(lin);
}

procedure {:layer 1} intro_write_vis(n: Invoc, s: SetInvoc)
  modifies vis;
  ensures {:layer 1} vis == old(vis)[n := s];
{
  vis[n] := s;
}

procedure {:layer 1} {:inline 1} intro_writeLin(n: Invoc)
  requires {:layer 1} !Seq_elem(n, lin);
  // To show that linearization is consistent with happens-before
  requires {:layer 1} (forall n1 : Invoc :: hb(n1, n) ==> Seq_elem(n1, lin));
  ensures {:layer 1} Seq_elem(n, lin);
  modifies lin;
{
  lin := Seq_append(lin, n);
}

// Special call and return actions  // TODO make these instrumentation stuff

procedure {:atomic} {:layer 1} spec_call_atomic(m: Method, k: Key)
  returns ({:linear "this"} this: Invoc)
  modifies called, returned;
{
  assume m == invoc_m(this) && k == invoc_k(this);
  // everything before this has returned
  assume (forall n1: Invoc :: hb(n1, this) ==> returned[n1]);
  // this has not been called or returned yet
  assume (!called[this] && !returned[this]);
  called[this] := true;
}
procedure {:yields} {:layer 0} {:refines "spec_call_atomic"}
  spec_call(m: Method, k: Key) returns ({:linear "this"} this: Invoc);

procedure {:atomic} {:layer 1} spec_return_atomic({:linear "this"} this: Invoc)
  modifies returned;
{
  returned[this] := true;
}
procedure {:yields} {:layer 0} {:refines "spec_return_atomic"}
  spec_return({:linear "this"} this: Invoc);


// ---------- queue methods:

procedure {:atomic} {:layer 2} pop_atomic() returns (k: Key)
  modifies lin, vis;
{
  var {:linear "this"} this: Invoc; var my_vis: SetInvoc;
  assume Queue.pop == invoc_m(this);

  // Satisfies its functional spec  // TODO check how Michael did this
  assume k == Queue.stateArray(Queue.ofSeq(lin))[Queue.stateHead(Queue.ofSeq(lin))];

  lin := Seq_append(lin, this);
  vis[this] := my_vis;
  // Is complete -- TODO make predicate  // TODO only writes in lin?
  assume my_vis == Set_ofSeq(lin);
}

procedure {:yields} {:layer 1} {:refines "pop_atomic"} pop() returns (k: Key)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
{
  var {:linear "this"} this: Invoc;
  var {:layer 1} my_vis: SetInvoc;
  var b: bool;
  var h, t, hn: Ref;

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);

  call this := spec_call(Queue.pop, k);
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  while (true)
    invariant {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  {
    call h := readHead();
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} h == head || usedFP[h];

    call t := readTail();
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} h == head || usedFP[h];
    assert {:layer 1} (h == head && h != t ==> head != tail);

    call hn := readNext(h);
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} h == head || usedFP[h];
    assert {:layer 1} (h == t && hn == null) || queueFP[hn] || usedFP[hn];
    assert {:layer 1} (h == head && h != t ==> head != tail && hn == next[head]);

    if (h != t) {
      call k := readData(hn);
      yield;
      assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
      assert {:layer 1} h == head || usedFP[h];
      assert {:layer 1} (h == head && h != t ==> head != tail && hn == next[head]);
      assert {:layer 1} data[hn] == k;

      call b := casHeadTransfer(h, hn, this);
      if (b) {
        // Linearization point.
        call intro_writeLin(this);
        call my_vis := intro_readLin();
        call intro_write_vis(this, my_vis);

        break;
      }
    }
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  }
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
  call spec_return(this);
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
}

procedure {:atomic} {:layer 2} push_atomic(k: Key, x: Ref,
    {:linear_in "FP"} xFP: [Ref]bool)
  modifies lin, vis;
{
  var {:linear "this"} this: Invoc; var my_vis: SetInvoc;
  assume Queue.push == invoc_m(this) && k == invoc_k(this);

  // Satisfies its functional spec
  assume true;

  lin := Seq_append(lin, this);
  vis[this] := my_vis;
  // Is complete -- TODO make predicate
  assume my_vis == Set_ofSeq(lin);
}

procedure {:yields} {:layer 1} {:refines "push_atomic"} push(k: Key, x: Ref,
    {:linear_in "FP"} xFP: [Ref]bool)
  requires {:layer 1} xFP[x] && next[x] == null && data[x] == k && nextTags[x] == Set_empty;  // TODO alloc x with k
  requires {:layer 1} !Btwn(next, head, x, null);  // TODO get from linearity
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
{
  var {:linear "this"} this: Invoc;
  var {:layer 1} my_vis: SetInvoc;
  var t, tn: Ref;
  var b: bool;
  var {:linear "FP"} tFP: [Ref]bool;

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  assert {:layer 1} !Btwn(next, head, x, null);
  assert {:layer 1} xFP[x] && next[x] == null && data[x] == k && nextTags[x] == Set_empty;

  call this := spec_call(Queue.push, k);
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  assert {:layer 1} !Btwn(next, head, x, null);
  assert {:layer 1} xFP[x] && next[x] == null && data[x] == k && nextTags[x] == Set_empty;
  tFP := xFP;
  while (true)
    invariant {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    invariant {:layer 1} known(x) && !Btwn(next, head, x, null);
    invariant {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k && nextTags[x] == Set_empty;
  {
    call t := readTail();
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k && nextTags[x] == Set_empty;
    assert {:layer 1} t != null && (queueFP[t] || usedFP[t]);
    assert {:layer 1} next[t] == null ==> queueFP[t];

    call tn := readNext(t);
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k && nextTags[x] == Set_empty;
    assert {:layer 1} t != null && (queueFP[t] || usedFP[t]);
    assert {:layer 1} next[t] == null ==> queueFP[t];
    assert {:layer 1} tn != null ==> tn == next[t];

    if (tn == null) {
      call b, tFP := casNextTransfer(t, tn, x, tFP, this);
      if (b) {
        // Linearization point.
        call intro_writeNextInvoc(t, this);
        call intro_writeAbsRefs(k, x);
        call intro_writeLin(this);
        call my_vis := intro_readLin();
        call intro_write_vis(this, my_vis);

        break;
      }
    } else {
      call b := casTail(t, tn, this);
    }
    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} !Btwn(next, head, x, null);
    assert {:layer 1} tFP == xFP && xFP[x] && next[x] == null && data[x] == k && nextTags[x] == Set_empty;
  }
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
  call spec_return(this);
  yield;
  assert {:expand} {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
}


procedure {:atomic} {:layer 2} size_atomic() returns (s: int)
  modifies lin, vis;
{
  var {:linear "this"} this: Invoc; var my_vis: SetInvoc;
  assume Queue.size == invoc_m(this);

  // Satisfies its functional spec
  assume s == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
    - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis)));

  lin := Seq_append(lin, this);
  vis[this] := my_vis;
  // Is monotonic
  assume (forall j: Invoc :: hb(j, this) ==> Set_subset(vis[j], my_vis));
}

procedure {:yields} {:layer 1} {:refines "size_atomic"} size() returns (s: int)
  requires {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  ensures {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
{
  var {:linear "this"} this: Invoc;
  var {:layer 1} my_vis: SetInvoc; var TODO: Key;
  var {:layer 1} t0i: int; var {:layer 1} ci: int;
  var {:layer 1} t0: Ref;
  var c, cn: Ref;
  var {:layer 1} old_vis: SetInvoc;
  var {:layer 1} old_c: Ref;

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);

  call this := spec_call(Queue.size, TODO);
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);

  s := 0;
  call c := readHead();
  call ci := intro_getHeadIndex();
  call t0 := intro_getTail();
  call t0i := intro_getTailIndex();
  call my_vis := intro_readLin();

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  assert {:layer 1} (forall j: Invoc :: hb(j, this) ==> Set_subset(vis[j], my_vis));
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, my_vis)}
    Set_elem(n1, my_vis) ==> Set_elem(n1, Set_ofSeq(lin)));
  assert {:layer 1} (usedFP[c] || queueFP[c]);
  assert {:layer 1} ci == Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis)));
  assert {:layer 1} t0i == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)));
  assert {:layer 1} known(t0) && t0 != null && Btwn(next, start, t0, null);
  assert {:layer 1} known(c) && Btwn(next, start, c, t0);
  assert {:layer 1} c == absRefs[ci - 1] && t0 == absRefs[t0i - 1];
  assert {:layer 1} (forall n: Invoc :: {Set_elem(n, my_vis)}
    known(nextRef[n]) && invoc_m(n) == Queue.push ==>
    (Set_elem(n, my_vis) <==> Btwn(next, start, nextRef[n], t0) && nextRef[n] != t0));
  assert {:layer 1} (forall n1, n2: Invoc :: {Seq_ord(lin, n1, n2)} known(nextRef[n2]) ==>
    (Seq_elem(n1, Seq_restr(lin, my_vis)) && Seq_elem(n2, lin) && !Set_elem(n2, my_vis)
    && invoc_m(n2) == Queue.push ==> Seq_ord(lin, n1, n2)));

  call cn := readNext(c);
  old_vis := my_vis;
  call my_vis := intro_readNextTags(c, my_vis);
  if (cn != null) {
    ci := ci + 1;
  }

  // Case 1
  assert {:layer 1} Btwn(next, start, c, t0) && c != t0
    ==> Set_elem(nextInvoc[c], old_vis);
  assert {:layer 1} Btwn(next, start, c, t0) && c != t0
    ==> old_vis == my_vis
    && t0i == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
    && ((cn == null && c == absRefs[ci - 1]) || (cn != null && c == absRefs[ci - 2]))
    && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis)));
  // Case 2  -- restr(lin, my_vis) == append(restr(lin, old_vis), nextInvoc[c])
  assert {:layer 1} Btwn(next, t0, c, null) && next[c] != null
    ==> Seq_restr(lin, my_vis) == Seq_append(Seq_restr(lin, old_vis), nextInvoc[c])
      && ci == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
      && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis)));

  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
  assert {:layer 1} (forall j: Invoc :: hb(j, this) ==> Set_subset(vis[j], my_vis));
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, my_vis)}
    Set_elem(n1, my_vis) ==> Set_elem(n1, Set_ofSeq(lin)));
  assert {:layer 1} (usedFP[c] || queueFP[c]) && known(c) && (cn != null ==> cn == next[c]);
  assert {:layer 1} cn == null ==> Btwn(next, t0, c, null);
  assert {:layer 1} ((cn == null && c == absRefs[ci - 1]) || (cn != null && c == absRefs[ci - 2])) && t0 == absRefs[t0i - 1];
  assert {:layer 1} known(t0) && t0 != null && Btwn(next, start, t0, null);
  assert {:layer 1} (Btwn(next, start, c, t0) && c != t0
      && t0i == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
      && (forall n: Invoc :: {Set_elem(n, my_vis)}
        known(nextRef[n]) && invoc_m(n) == Queue.push ==>
        (Set_elem(n, my_vis) <==> Btwn(next, start, nextRef[n], t0) && nextRef[n] != t0))
      && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))
    || (Btwn(next, t0, c, null)
      && ci == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
      && (forall n: Invoc :: {Set_elem(n, my_vis)}
        known(nextRef[n]) && invoc_m(n) == Queue.push ==>
        (Set_elem(n, my_vis) <==> Btwn(next, start, nextRef[n], c) && (cn != null || nextRef[n] != c)))
      && ((cn == null && s == ci - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))
        || (cn != null && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))));
  assert {:layer 1} (forall n1, n2: Invoc :: {Seq_ord(lin, n1, n2)} known(nextRef[n2]) ==>
    (Seq_elem(n1, Seq_restr(lin, my_vis)) && Seq_elem(n2, lin) && !Set_elem(n2, my_vis)
    && invoc_m(n2) == Queue.push ==> Seq_ord(lin, n1, n2)));

  while (cn != null)
    invariant {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    invariant {:layer 1} (forall j: Invoc ::
      hb(j, this) ==> Set_subset(vis[j], my_vis));
    invariant {:layer 1} (forall n1: Invoc :: {Set_elem(n1, my_vis)}
      Set_elem(n1, my_vis) ==> Set_elem(n1, Set_ofSeq(lin)));
    invariant {:layer 1} known(c) && (usedFP[c] || queueFP[c]);
    invariant {:layer 1} known(cn) && (cn != null ==> next[c] == cn);
    invariant {:layer 1} cn == null ==> Btwn(next, t0, c, null);
    invariant {:layer 1} known(t0) && t0 != null && Btwn(next, start, t0, null);
    invariant {:layer 1} ((cn == null && c == absRefs[ci - 1]) || (cn != null && c == absRefs[ci - 2])) && t0 == absRefs[t0i - 1];
    invariant {:layer 1} (Btwn(next, start, c, t0) && c != t0
        && t0i == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
        && (forall n: Invoc :: {Set_elem(n, my_vis)}
          known(nextRef[n]) && invoc_m(n) == Queue.push ==>
          (Set_elem(n, my_vis) <==> Btwn(next, start, nextRef[n], t0) && nextRef[n] != t0))
        && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))
      || (Btwn(next, t0, c, null)
        && ci == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
        && (forall n: Invoc :: {Set_elem(n, my_vis)}
          known(nextRef[n]) && invoc_m(n) == Queue.push ==>
          (Set_elem(n, my_vis) <==> Btwn(next, start, nextRef[n], c)
            && (cn != null || nextRef[n] != c)))
        && ((cn == null && s == ci - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))
          || (cn != null && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))));
    invariant {:layer 1} (forall n1, n2: Invoc :: {Seq_ord(lin, n1, n2)} known(nextRef[n2]) ==>
      (Seq_elem(n1, Seq_restr(lin, my_vis)) && Seq_elem(n2, lin) && !Set_elem(n2, my_vis)
      && invoc_m(n2) == Queue.push ==> Seq_ord(lin, n1, n2)));
  {
    old_vis := my_vis; old_c := c;

    s := s + 1;
    c := cn;
    call cn := readNext(c);
    call my_vis := intro_readNextTags(c, my_vis);
    if (cn != null) {
      ci := ci + 1;
    }

    // Case 1
    assert {:layer 1} Btwn(next, start, c, t0) && c != t0
      ==> Set_elem(nextInvoc[c], old_vis);
    assert {:layer 1} Btwn(next, start, c, t0) && c != t0
      ==> old_vis == my_vis
      && t0i == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
      && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis)));
    // Case 2  -- restr(lin, my_vis) == append(restr(lin, old_vis), nextInvoc[c])
    assert {:layer 1} Btwn(next, t0, c, null) && next[c] != null
      ==> Seq_restr(lin, my_vis) == Seq_append(Seq_restr(lin, old_vis), nextInvoc[c]);
    assert {:layer 1} Btwn(next, t0, c, null) && next[c] != null
      && Btwn(next, start, old_c, t0) && old_c != t0
      ==> c == t0 && next[old_c] == t0;
    assert {:layer 1} Btwn(next, t0, c, null) && next[c] != null
      && Btwn(next, start, old_c, t0) && old_c != t0
      ==> ci == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)));
    assert {:layer 1} Btwn(next, t0, c, null) && next[c] != null
      ==> ci == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)));
    assert {:layer 1} Btwn(next, t0, c, null) && next[c] != null
      ==> s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis)));

    yield;
    assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} (forall j: Invoc ::
      hb(j, this) ==> Set_subset(vis[j], my_vis));
    assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, my_vis)}
      Set_elem(n1, my_vis) ==> Set_elem(n1, Set_ofSeq(lin)));
    assert {:layer 1} known(c) && (usedFP[c] || queueFP[c]);
    assert {:layer 1} known(cn) && (cn != null ==> next[c] == cn);
    assert {:layer 1} cn == null ==> Btwn(next, t0, c, null);
    assert {:layer 1} known(t0) && t0 != null && Btwn(next, start, t0, null);
    assert {:layer 1} ((cn == null && c == absRefs[ci - 1]) || (cn != null && c == absRefs[ci - 2])) && t0 == absRefs[t0i - 1];
    assert {:layer 1} (Btwn(next, start, c, t0) && c != t0
        && t0i == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
        && (forall n: Invoc :: {Set_elem(n, my_vis)}
          known(nextRef[n]) && invoc_m(n) == Queue.push ==>
          (Set_elem(n, my_vis) <==> Btwn(next, start, nextRef[n], t0) && nextRef[n] != t0))
        && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))
      || (Btwn(next, t0, c, null)
        && ci == Queue.stateTail(Queue.ofSeq(Seq_restr(lin, my_vis)))
        && (forall n: Invoc :: {Set_elem(n, my_vis)}
          known(nextRef[n]) && invoc_m(n) == Queue.push ==>
          (Set_elem(n, my_vis) <==> Btwn(next, start, nextRef[n], c)
            && (cn != null || nextRef[n] != c)))
        && ((cn == null && s == ci - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))
          || (cn != null && s == ci - 1 - Queue.stateHead(Queue.ofSeq(Seq_restr(lin, my_vis))))));
    assert {:layer 1} (forall n1, n2: Invoc :: {Seq_ord(lin, n1, n2)} known(nextRef[n2]) ==>
      (Seq_elem(n1, Seq_restr(lin, my_vis)) && Seq_elem(n2, lin) && !Set_elem(n2, my_vis)
      && invoc_m(n2) == Queue.push ==> Seq_ord(lin, n1, n2)));
  }

  // Linearization point.
  call intro_writeLin(this);
  call intro_write_vis(this, my_vis);
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned) && postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));

  call spec_return(this);
  yield;
  assert {:layer 1} Inv(queueFP, usedFP, start, head, tail, next, data, nextTags, nextInvoc, nextRef, lin, vis, absRefs, called, returned);
  return;
}
