// A simplified hash table implementation with weakly consistent contains method


// ---------- Encoding of weak visibility

type Invoc;

// Create an invocation. Methods are: 0 - put, 1 - get, 2 - contains
function createInvoc(m: int, k: int, v: int) returns (i: Invoc);


type SeqInvoc;  // sequence of invocations


function subseq(s: SeqInvoc, t: SeqInvoc) : bool;

// subseq is reflexive
axiom (forall s: SeqInvoc :: subseq(s, s));

// subseq is transitive
axiom (forall s, t, u: SeqInvoc :: subseq(s, t) && subseq(t, u) ==> subseq(s, u));


function append(s: SeqInvoc, o: Invoc) returns (t: SeqInvoc);

// append preserves subseq
axiom (forall s, t: SeqInvoc, o: Invoc :: subseq(s, t) ==> subseq(append(s, o), append(t, o)));


function union(s1: SeqInvoc, s2: SeqInvoc) returns (t: SeqInvoc);

// union is idempotent
axiom (forall s: SeqInvoc :: s == union(s, s));

// union is associative
axiom (forall s, t: SeqInvoc :: union(s, t) == union(t, s));

// union is monotonic w.r.t subseq
axiom (forall s, t1, t2: SeqInvoc :: subseq(t1, t2) ==> subseq(union(s, t1), union(s, t2)));


// A function to restrict a SeqInvoc to invocations involving key k
function restr(s: SeqInvoc, k: int) returns (t: SeqInvoc);

// restr is a subseq
axiom (forall s: SeqInvoc, k: int :: subseq(restr(s, k), s));


// A function to calculate the abstract state after a sequential execution
function state(s: SeqInvoc) returns (m: [int]int);


// ---------- Some lemmas that we need

// The mapping of key k depends only invocations involving k
axiom (forall s: SeqInvoc, k: int :: state(s)[k] == state(restr(s, k))[k]);

// Adding invocations of a key k does not affect state of keys k1 != k
axiom (forall s, t: SeqInvoc, k, k1: int :: k != k1 ==> state(union(s, restr(t, k)))[k1] == state(s)[k1]);

// The effect of appending an invocation on key k on state of other keys
axiom (forall s1, s2: SeqInvoc, o: Invoc, m, k, v: int ::
        s2 == append(s1, o) && o == createInvoc(m, k, v) ==>
          (forall i: int :: i != k ==> state(s1)[i] == state(s2)[i])
);

// The effect of appending an invocation on key k on state of k
axiom (forall s1, s2: SeqInvoc, o: Invoc, m, k, v: int ::
        s2 == append(s1, o) && o == createInvoc(m, k, v) ==>
          (m == 0 ==> state(s2)[k] == v)
          && (m == 1 || m == 2 ==> state(s2)[k] == state(s1)[k])
);

// Taking union of a restriction of a super-sequence means restrictions are same
axiom (forall s0, s1, t: SeqInvoc, k: int ::
        s1 == union(s0, restr(t, k)) && subseq(s0, t) ==>
          restr(s1, k) == restr(t, k)
);


// ---------- Logical and concrete shared state

// A shared global variable that builds the linearization
var {:layer 0,2} lin: SeqInvoc;

// Concrete state of implementation
var {:layer 0,2} table: [int]int;
const tableLen: int;
axiom 0 <= tableLen;

// Invariant
function {:inline} tableInv(table: [int]int, lin: SeqInvoc) : bool
{
  (forall i: int :: 0 <= i && i < tableLen ==> table[i] == state(lin)[i])
}


// ---------- Primitives/helpers for modifying global state

// These are essentially the same as get/put because I don't know how to enforce
// that the write/read of the table and the append to lin happen at the same time

procedure {:atomic} {:layer 1} writeTable_spec(k, v: int)
  modifies table, lin;
{
  table[k] := v;
  lin := append(lin, createInvoc(0, k, v));
}

procedure {:yields} {:layer 0} {:refines "writeTable_spec"} writeTable(k, v: int);

procedure {:atomic} {:layer 1} readTable_spec(k: int) returns (v: int)
  modifies lin;
{
  v := table[k];
  lin := append(lin, createInvoc(1, k, v));
}

procedure {:yields} {:layer 0} {:refines "readTable_spec"} readTable(k: int)
  returns (v: int);


// ---------- Procedures/methods

procedure {:atomic} {:layer 2} put_spec(k: int, v: int)
  modifies table, lin;
{
  table[k] := v;
  lin := append(lin, createInvoc(0, k, v));
}

procedure {:yields} {:layer 1} {:refines "put_spec"}  put(k, v: int)
  requires {:layer 1} tableInv(table, lin);
  ensures {:layer 1} tableInv(table, lin);
{
  yield;
  assert {:layer 1} tableInv(table, lin);
  call writeTable(k, v);
  yield;
  assert {:layer 1} tableInv(table, lin);
}


procedure {:atomic} {:layer 2} get_spec(k: int) returns (v: int)
  modifies lin;
{
  v := table[k];
  lin := append(lin, createInvoc(1, k, v));
}

procedure {:yields} {:layer 1} {:refines "get_spec"}  get(k, v: int)
  requires {:layer 1} tableInv(table, lin);
  ensures {:layer 1} tableInv(table, lin);
{
