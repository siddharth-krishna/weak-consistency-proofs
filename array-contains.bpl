// A simplified hash table implementation with weakly consistent contains method


// ---------- Types and axiomatization of sequences of invocations

type Invoc;

// function key(n: Invoc) returns (k: int);

type Method;
const unique get, put, contains: Method;

// Create an invocation.
function createInvoc(m: Method, k: int, v: int) returns (i: Invoc);


// Sequences of invocations
type SeqInvoc;

function append(s: SeqInvoc, o: Invoc) returns (t: SeqInvoc);

/*
// append preserves subset
axiom (forall s, t: SeqInvoc, o: Invoc :: subset(s, t) ==>
        subset(append(s, o), append(t, o)));
axiom (forall s, t: SeqInvoc, o: Invoc :: subset(s, t) ==>
        subset(s, append(t, o)));
*/


// Sets of invocations -- TODO Z3 support?
type SetInvoc;
const emptySet: SetInvoc;

// function elementOf(n: Invoc, s: SetInvoc) : bool;

function subset(s: SetInvoc, t: SetInvoc) : bool;

// emptySet is a subset of anything
axiom (forall s: SetInvoc :: subset(emptySet, s));

// subset is reflexive
axiom (forall s: SetInvoc :: subset(s, s));

// subset is transitive
axiom (forall s, t, u: SetInvoc :: subset(s, t) && subset(t, u) ==> subset(s, u));

function union(s1: SetInvoc, s2: SetInvoc) returns (t: SetInvoc);

// union is idempotent
axiom (forall s: SetInvoc :: s == union(s, s));

// union is associative
axiom (forall s, t: SetInvoc :: union(s, t) == union(t, s));

// union is monotonic w.r.t subset
axiom (forall s, t1, t2: SetInvoc :: subset(t1, t2) ==> subset(union(s, t1), union(s, t2)));

// Calculate the union of m[i] \cup ... \cup m[j-1]
function unionRange(m: [int]SetInvoc, i: int, j: int) returns (s: SetInvoc);

function setOfSeq(q: SeqInvoc) returns (s: SetInvoc);

function add(s: SetInvoc, n: Invoc) returns (t: SetInvoc);

// add preserves subset relation
axiom (forall s, t: SetInvoc, n: Invoc :: subset(s, t) ==> subset(add(s, n), add(t, n)));
axiom (forall s, t: SetInvoc, n: Invoc :: subset(s, t) ==> subset(s, add(t, n)));

// Relation between setOfSeq, add, and append
axiom (forall q: SeqInvoc, n: Invoc :: setOfSeq(append(q, n)) == add(setOfSeq(q), n));

// Relation between unionRange, add, and append
axiom (forall t: [int]SetInvoc, i, j, k: int, q: SeqInvoc, n: Invoc ::
        unionRange(t, i, j) == setOfSeq(q) && i <= k && k < j ==>
          unionRange(t[k := add(t[k], n)], i, j) == setOfSeq(append(q, n)));

// Add n to m[i], ..., m[j-1]
function addRange(m: [int]SetInvoc, n: Invoc, i: int, j: int)
  returns (m1: [int]SetInvoc);

// The effect of addRange
axiom (forall m, m1: [int]SetInvoc, n: Invoc, i: int, j: int, k: int ::
        m1 == addRange(m, n, i, j) && i <= k && k < j
        ==> m1[k] == add(m[k], n));
axiom (forall m, m1: [int]SetInvoc, n: Invoc, i: int, j: int, k: int ::
        m1 == addRange(m, n, i, j) && !(i <= k && k < j)
        ==> m1[k] == m[k]);

// What happens to unionRange and setOfSeq when you do an addRange
axiom (forall t: [int]SetInvoc, i, j, i1, j1: int, q: SeqInvoc, n: Invoc ::
        unionRange(t, i, j) == setOfSeq(q) && i <= i1 && i1 < j1 && j1 <= j ==>
          unionRange(addRange(t, n, i1, j1), i, j) == setOfSeq(append(q, n)));

// A function to restrict a SetInvoc to invocations involving key k
function restr(s: SetInvoc, k: int) returns (t: SetInvoc);

// restr is a subset
axiom (forall s: SetInvoc, k: int :: subset(restr(s, k), s));

// restr is monotonic w.r.t subset
axiom (forall s, t: SetInvoc, k: int :: subset(s, t) ==> subset(restr(s, k), restr(t, k)));

// Adding an invocation on k increases restr
axiom (forall q: SeqInvoc, n: Invoc, m: Method, k, v: int :: n == createInvoc(m, k, v) ==>
        restr(setOfSeq(append(q, n)), k) == add(restr(setOfSeq(q), k), n)
);

// Adding invocations not on k preserves restr
axiom (forall q: SeqInvoc, n: Invoc, m: Method, k, k1, v: int ::
        n == createInvoc(m, k1, v) && k1 != k ==>
        restr(setOfSeq(append(q, n)), k) == restr(setOfSeq(q), k)
);

type AbsState = [int]int; // Abstract state

// A function to calculate the abstract state after executing a subset vis of
// a sequence of invocations lin
function state(vis: SetInvoc, lin: SeqInvoc) returns (m: AbsState);


// ---------- Some lemmas of this ADT that we need

// The effect of appending an invocation on key k on state of k
axiom (forall s1, s2: SetInvoc, q1, q2: SeqInvoc, n: Invoc, m: Method, k, v: int ::
        n == createInvoc(m, k, v) && q2 == append(q1, n) && s2 == add(s1, n) ==>
          (m == put ==> state(s2, q2)[k] == v)
);
axiom (forall s1, s2: SetInvoc, q1, q2: SeqInvoc, n: Invoc, m: Method, k, v: int ::
        n == createInvoc(m, k, v) && q2 == append(q1, n) && s2 == add(s1, n) ==>
          ((m == get || m == contains) ==> state(s2, q2)[k] == state(s1, q1)[k])
);
// TODO why doesn't this follow from the above?
axiom (forall t1, t2: [int]SetInvoc, q1, q2: SeqInvoc, n: Invoc, i, j, k, k1, v: int ::
        n == createInvoc(contains, k, v) && q2 == append(q1, n)
        && t2 == addRange(t1, n, i, j) ==>
          state(t2[k1], q2)[k1] == state(t1[k1], q1)[k1]
);


// The effect of appending an invocation on key k on state with unchanged vis
axiom (forall s: SetInvoc, q1, q2: SeqInvoc, n: Invoc, m: Method, k, k1, v: int ::
        n == createInvoc(m, k, v) && q2 == append(q1, n) ==>
          state(s, q1)[k1] == state(s, q2)[k1]
);


// The mapping of key k depends only invocations involving k
axiom (forall s: SetInvoc, q: SeqInvoc, k: int ::
        state(s, q)[k] == state(restr(s, k), q)[k]);
axiom (forall q: SeqInvoc, k: int ::
        state(setOfSeq(q), q)[k] == state(restr(setOfSeq(q), k), q)[k]);

// Taking union with a restriction of a super-set means restrictions are same
axiom (forall s0, s1, t: SetInvoc, k: int ::
        s1 == union(s0, t) && subset(restr(s0, k), t) ==>
          restr(s1, k) == restr(t, k)
);

/*
// Adding invocations of a key k does not affect state of keys k1 != k
axiom (forall s, t: SeqInvoc, k, k1: int :: k != k1 ==>
        state(union(s, restr(t, k)))[k1] == state(s)[k1]);

*/


// ---------- Representation of execution and linearization

// A shared global variable that builds the linearization
var {:layer 1,2} lin: SeqInvoc;

// hb(x, y) : x happens-before y.
// We assume there exists such a function, given by the client program
function hb(x: Invoc, y: Invoc) : bool;

// The set of invocations that have been called
var {:layer 0,1} called: [Invoc]bool;

// The set of invocations that have returned
var {:layer 0,1} returned: [Invoc]bool;

// A map from invocations to the set of prior invocations visible to them
var vis: [Invoc]SetInvoc;

// The invariants satisfied by the above
function {:inline} linInv(lin: SeqInvoc, abs: AbsState, tabvis: [int]SetInvoc)
  : bool
{
  (forall i: int :: 0 <= i && i < tableLen ==> state(tabvis[i], lin)[i] == abs[i])
  && (forall i: int :: 0 <= i && i < tableLen ==>
      state(tabvis[i], lin)[i] == state(restr(setOfSeq(lin), i), lin)[i])
  && (forall i: int :: 0 <= i && i < tableLen ==> subset(restr(setOfSeq(lin), i), tabvis[i]))
  // The linearization is consistent with happens-before
}

// ---------- Logical and concrete shared state

// Abstract state of ADT
var {:layer 1,2} abs: AbsState;

// Visibility per location of concrete state
var {:layer 0,1} tabvis: [int]SetInvoc;


// Concrete state of implementation
var {:layer 0,1} table: [int]int;
const tableLen: int;
axiom 0 <= tableLen;


function {:inline} abstracts(conc: [int]int, abs: AbsState) : bool
{
  (forall i: int :: 0 <= i && i < tableLen ==> conc[i] == abs[i])
}

// Invariant
function {:inline} tableInv(table: [int]int, abs: AbsState, tabvis: [int]SetInvoc,
                            lin: SeqInvoc) : bool
{
  abstracts(table, abs)
  && unionRange(tabvis, 0, tableLen) == setOfSeq(lin)
  && linInv(lin, abs, tabvis)
}


// ---------- Primitives/helpers for modifying global state

// Write to the table and returns the union of tabvis as the visibility
procedure {:atomic} {:layer 1} writeTable_spec(k, v: int, n: Invoc)
  returns (my_vis: SetInvoc, old_tabvis: [int]SetInvoc)
  modifies table, vis, tabvis;
{
  old_tabvis := tabvis;
  table[k] := v;

  tabvis[k] := add(tabvis[k], n);
  assume my_vis == unionRange(tabvis, 0, tableLen);
  vis[n] := my_vis;
}
procedure {:yields} {:layer 0} {:refines "writeTable_spec"}
  writeTable(k, v: int, n: Invoc) returns (my_vis: SetInvoc, old_tabvis: [int]SetInvoc);

// Read from the table and returns the union of tabvis as the visibility
procedure {:atomic} {:layer 1} readTable_spec(k: int, n: Invoc)
  returns (v: int, my_vis: SetInvoc)
  modifies vis, tabvis;
{
  v := table[k];

  tabvis[k] := add(tabvis[k], n);
  assume my_vis == unionRange(tabvis, 0, tableLen);
  vis[n] := my_vis;
}
procedure {:yields} {:layer 0} {:refines "readTable_spec"} readTable(k: int, n: Invoc)
  returns (v: int, my_vis: SetInvoc);


// Read from the table and add the tabvis entry to the visibility
procedure {:atomic} {:layer 1} readTable1_spec(k: int, my_vis: SetInvoc)
  returns (v: int, old_vis, new_vis: SetInvoc)
{
  v := table[k];

  old_vis := my_vis;
  new_vis := union(my_vis, tabvis[k]);
}
procedure {:yields} {:layer 0} {:refines "readTable1_spec"}
  readTable1(k: int, my_vis: SetInvoc) returns (v: int, old_vis, new_vis: SetInvoc);


// Write my_vis to vis, and also add my label n to all of tabvis[]  -- TODO rename
procedure {:atomic} {:layer 1} addVis_spec(n: Invoc, my_vis: SetInvoc, i: int)
  returns (old_tabvis: [int]SetInvoc)
  modifies vis, tabvis;
{
  old_tabvis := tabvis;
  vis[n] := my_vis;
  tabvis := addRange(tabvis, n, 0, i+1);
}
procedure {:yields} {:layer 0} {:refines "addVis_spec"}
  addVis(n: Invoc, my_vis: SetInvoc, i: int)  returns (old_tabvis: [int]SetInvoc);


// Introduction actions:

procedure {:layer 1} {:inline 1} intro_writeLin1(n: Invoc) returns (old_lin: SeqInvoc)
  modifies lin;
{
  old_lin := lin;
  lin := append(lin, n);
}

procedure {:layer 1} {:inline 1} intro_writeLin(n: Invoc)
  modifies lin;
{
  lin := append(lin, n);
}

procedure {:layer 1} {:inline 1} intro_writeAbs(k: int, v: int)
  modifies abs;
{
  abs[k] := v;
}

// Special call and return actions

procedure {:atomic} {:layer 1} spec_call_spec(n: Invoc)
  modifies called;
{
  called[n] := true;
}
procedure {:yields} {:layer 0} {:refines "spec_call_spec"} spec_call(n: Invoc);

procedure {:atomic} {:layer 1} spec_return_spec(n: Invoc)
  modifies returned;
{
  returned[n] := true;
}
procedure {:yields} {:layer 0} {:refines "spec_return_spec"}  spec_return(n: Invoc);


// ---------- The ADT methods

procedure {:atomic} {:layer 2} put_spec(k: int, v: int)
  returns (my_vis: SetInvoc)
  modifies abs, lin, vis;
{
  var this: Invoc;
  this := createInvoc(put, k, v);
  lin := append(lin, this);
  vis := vis[this := my_vis];
  // Put is complete
  assume my_vis == setOfSeq(lin);

  // Put satisfies its functional spec
  abs[k] := v;
}

procedure {:yields} {:layer 1} {:refines "put_spec"} put(k, v: int)
  returns (my_vis: SetInvoc)
  requires {:layer 1} tableInv(table, abs, tabvis, lin);
  requires {:layer 1} 0 <= k && k < tableLen;
  ensures {:layer 1} tableInv(table, abs, tabvis, lin);
{
  var this: Invoc; var old_tabvis: [int]SetInvoc;
  this := createInvoc(put, k, v);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin);
  call spec_call(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin);

  call my_vis, old_tabvis := writeTable(k, v, this);

  call intro_writeAbs(k, v);
  call intro_writeLin(this);

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin);
  call spec_return(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin);
}

procedure {:atomic} {:layer 2} get_spec(k: int) returns (v: int, my_vis: SetInvoc)
  modifies lin, vis;
{
  var this: Invoc;
  this := createInvoc(get, k, v);
  lin := append(lin, this);
  vis := vis[this := my_vis];
  // Get is complete -- TODO make predicate
  assume my_vis == setOfSeq(lin);

  // Get satisfies its functional spec
  v := abs[k];
}

procedure {:yields} {:layer 1} {:refines "get_spec"} get(k: int)
  returns (v: int, my_vis: SetInvoc)
  requires {:layer 1} tableInv(table, abs, tabvis, lin);
  requires {:layer 1} 0 <= k && k < tableLen;
  ensures {:layer 1} tableInv(table, abs, tabvis, lin);
{
  var this: Invoc;
  this := createInvoc(get, k, v);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin);
  call spec_call(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin);

  call v, my_vis := readTable(k, this);

  call intro_writeLin(this);

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin);
  call spec_return(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin);
}


function contains_func_spec(vis: SetInvoc, lin: SeqInvoc, witness_k: int,
                            v: int, res: bool) : bool
{
   (res ==> state(vis, lin)[witness_k] == v)
   && (!res ==> (forall i: int :: 0 <= i && i < tableLen ==> state(vis, lin)[i] != v))
}

procedure {:atomic} {:layer 2} contains_spec(v: int)
  returns (res: bool, my_vis: SetInvoc, witness_k: int)
  modifies lin, vis;
{
  var this: Invoc;
  this := createInvoc(contains, witness_k, v);
  lin := append(lin, createInvoc(contains, witness_k, v));
  vis := vis[this := my_vis];
  // Contains is monotonic
  assume (forall j: Invoc :: hb(j, this) ==> subset(vis[j], my_vis));

  // Contains satisfies its functional spec
  assume contains_func_spec(my_vis, lin, witness_k, v, res);
}

procedure {:yields} {:layer 1} {:refines "contains_spec"} contains(v: int)
  returns (res: bool, my_vis: SetInvoc, witness_k: int)
  requires {:layer 1} tableInv(table, abs, tabvis, lin);
  ensures {:layer 1} tableInv(table, abs, tabvis, lin);
{
  var k, tv: int;
  var old_vis: SetInvoc;
  var this: Invoc;
  var old_tabvis: [int]SetInvoc; var {:layer 1} old_lin: SeqInvoc;

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin);
  k := 0;
  my_vis := emptySet;
  while (k < tableLen)
    invariant {:layer 1} 0 <= k && k <= tableLen;
    invariant {:layer 1} (forall i: int :: 0 <= i && i < k ==> state(my_vis, lin)[i] != v);
    invariant {:layer 1} subset(my_vis, setOfSeq(lin));
    invariant {:layer 1} tableInv(table, abs, tabvis, lin);
  {
    // Read table[k] and add tabvis[k] to my_vis
    call tv, old_vis, my_vis := readTable1(k, my_vis);

    // tv == table[k] == abs[k] == state(tabvis[k], lin)[k]
    // old_vis < setOfSeq(lin) ==> restr(old_vis, k) < restr(setOfSeq(lin), k)
    assert {:layer 1} subset(restr(old_vis, k), restr(setOfSeq(lin), k));
    // linInv() ==> restr(setOfSeq(lin), k) < tabvis[k]
    // axiom ==> restr(my_vis, k) == restr(tabvis[k], k)
    assert {:layer 1} state(restr(my_vis, k), lin)[k]
                        == state(restr(tabvis[k], k), lin)[k];
    // == tv
    yield; assert {:layer 1} tableInv(table, abs, tabvis, lin) && tv == state(my_vis, lin)[k];

    if (tv == v) {
      // Linearization point
      this := createInvoc(contains, k, v);
      my_vis := add(my_vis, this);
      witness_k := k;
      call old_tabvis := addVis(this, my_vis, k);
      call old_lin := intro_writeLin1(this);

      res := true;

      assert {:layer 1} (forall i: int :: 0 <= i && i < tableLen ==>
                           state(tabvis[i], lin)[i] == abs[i]);
      assert {:layer 1} (forall i: int :: k < i && i < tableLen ==>
                           subset(restr(setOfSeq(lin), i), tabvis[i]));
      assert {:layer 1} (forall i: int :: 0 <= i && i < k ==>
                           restr(setOfSeq(lin), i) == restr(setOfSeq(old_lin), i)
                           && tabvis[i] == add(old_tabvis[i], this));
      assert {:layer 1} (forall i: int :: 0 <= i && i < k ==>
                           restr(setOfSeq(lin), i) == restr(setOfSeq(old_lin), i));
      assert {:layer 1} (restr(setOfSeq(lin), k)
                            == add(restr(setOfSeq(old_lin), k), this)
                          && tabvis[k] == add(old_tabvis[k], this));
      assert {:layer 1} (subset(restr(setOfSeq(lin), k), tabvis[k]));

      // CONTINUE here: need to prove monotonicity
      yield; assert {:layer 1} tableInv(table, abs, tabvis, lin);
      return;
    }
    yield; assert {:layer 1} tableInv(table, abs, tabvis, lin);

    k := k + 1;
  }
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin);

  // Linearization point
  this := createInvoc(contains, k, v);
  my_vis := add(my_vis, this);
  witness_k := k;
  call old_tabvis := addVis(this, my_vis, k-1);
  call old_lin := intro_writeLin1(this);

  res := false;

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin);
  return;
}


// How to create a constant map with a default value, using a Z3 builtin
// function {:builtin "MapConst"} createMapConst(bool) : [Invoc]bool;

