// A simplified hash table implementation with weakly consistent contains method


// ---------- Types and axiomatization of sequences of invocations

type Method;
const unique get, put, contains: Method;

type Invoc;
function invoc_m(n: Invoc) : Method;
function invoc_k(n: Invoc) : int;
function invoc_v(n: Invoc) : int;

// Boilerplate stuff for linear variables
function {:builtin "MapConst"} MapConstBool(bool) : [Invoc]bool;
function {:inline} {:linear "this"} TidCollector(x: Invoc) : [Invoc]bool
{
  MapConstBool(false)[x := true]
}


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


// Sets of invocations -- TODO Z3 supports sets?
type SetInvoc;
const emptySet: SetInvoc;

function elem(n: Invoc, s: SetInvoc) : bool;

function subset(s: SetInvoc, t: SetInvoc) : bool;

// emptySet is a subset of anything
axiom (forall s: SetInvoc :: subset(emptySet, s));

// Nothing is an elem of emptySet
axiom (forall n: Invoc :: !elem(n, emptySet));

// subset is reflexive
axiom (forall s: SetInvoc :: subset(s, s));

// subset is transitive
axiom (forall s, t, u: SetInvoc :: subset(s, t) && subset(t, u) ==> subset(s, u));

// definition of subset in terms of elem
axiom (forall s, t: SetInvoc :: (forall n: Invoc :: elem(n, s) ==> elem(n, t)) ==> subset(s, t));

function union(s1: SetInvoc, s2: SetInvoc) returns (t: SetInvoc);

// union is idempotent
axiom (forall s: SetInvoc :: s == union(s, s));

// union is associative
axiom (forall s, t: SetInvoc :: union(s, t) == union(t, s));

// union is monotonic w.r.t subset
axiom (forall s, t1, t2: SetInvoc :: subset(t1, t2) ==> subset(union(s, t1), union(s, t2)));

axiom (forall s, t1, t2: SetInvoc :: subset(t1, s) && subset(t2, s) ==> subset(union(t1, t2), s));

// relation between union and elem
axiom (forall n: Invoc, s, s1, t: SetInvoc :: elem(n, s) && s1 == union(s, t) ==> elem(n, s1));

// Calculate the union m[i] \cup ... \cup m[j-1]
function unionRange(m: [int]SetInvoc, i: int, j: int) returns (s: SetInvoc);

// Relation between unionRange and add
/*
axiom (forall m: [int]SetInvoc, i, j: int ::{unionRange(m, i, j)}
       (forall s: SetInvoc, n: Invoc ::
       s == unionRange(m, i, j) && elem(n, s) ==> (exists k : int :: elem(n, m[k]))));
*/

function setOfSeq(q: SeqInvoc) returns (s: SetInvoc);

function add(s: SetInvoc, n: Invoc) returns (t: SetInvoc);

// Relation between add and elem
axiom (forall s: SetInvoc, n1, n2: Invoc :: elem(n1, add(s, n2))
       ==> n1 == n2 || elem(n1, s));
axiom (forall s: SetInvoc, n1, n2: Invoc :: elem(n1, s) ==> elem(n1, add(s, n2)));

// Relation between union and elem
axiom (forall s, t: SetInvoc, n1: Invoc :: elem(n1, union(s, t))
       ==> elem(n1, s) || elem(n1, t));

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
axiom (forall q: SeqInvoc, n: Invoc :: restr(setOfSeq(append(q, n)), invoc_k(n))
       == add(restr(setOfSeq(q), invoc_k(n)), n));

// Adding invocations not on k preserves restr
axiom (forall q: SeqInvoc, n: Invoc, k: int :: invoc_k(n) != k
       ==> restr(setOfSeq(append(q, n)), k) == restr(setOfSeq(q), k));

type AbsState = [int]int; // Abstract state

// A function to calculate the abstract state after executing a subset vis of
// a sequence of invocations lin
function state(vis: SetInvoc, lin: SeqInvoc) returns (m: AbsState);


// ---------- Some lemmas of this ADT that we need

// The effect of appending an invocation on key k on state of k
axiom (forall s1, s2: SetInvoc, q1, q2: SeqInvoc, n: Invoc ::
       q2 == append(q1, n) && s2 == add(s1, n)
       ==> (invoc_m(n) == put ==> state(s2, q2)[invoc_k(n)] == invoc_v(n)));

// Appending a get/contains invocation does not change state
axiom (forall s1, s2: SetInvoc, q1, q2: SeqInvoc, n: Invoc, k: int ::
       q2 == append(q1, n) && s2 == add(s1, n)
       && (invoc_m(n) == get || invoc_m(n) == contains)
       ==> state(s2, q2)[k] == state(s1, q1)[k]);

// The effect of appending an invocation on key k on state with unchanged vis
axiom (forall s: SetInvoc, q1: SeqInvoc, n: Invoc, k: int ::
          state(s, q1)[k] == state(s, append(q1, n))[k]);


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


// ---------- Logical and concrete shared state

// Abstract state of ADT
var {:layer 1,2} abs: AbsState;

// Visibility per location of concrete state
var {:layer 1,1} tabvis: [int]SetInvoc;


// Concrete state of implementation
var {:layer 0,1} table: [int]int;
const tabLen: int;
axiom 0 < tabLen;


function {:inline} abstracts(conc: [int]int, abs: AbsState) : bool
{
  (forall i: int :: 0 <= i && i < tabLen ==> conc[i] == abs[i])
}

// The invariants
function {:inline} tableInv(table: [int]int, abs: AbsState, tabvis: [int]SetInvoc,
                            lin: SeqInvoc, vis: [Invoc]SetInvoc, tabLen: int,
                            called: [Invoc]bool, returned: [Invoc]bool) : bool
{
  abstracts(table, abs)
  && unionRange(tabvis, 0, tabLen) == setOfSeq(lin)
  && (forall i: int :: 0 <= i && i < tabLen ==> state(tabvis[i], lin)[i] == abs[i])
  && (forall i: int :: 0 <= i && i < tabLen ==>
      state(tabvis[i], lin)[i] == state(restr(setOfSeq(lin), i), lin)[i])
  && (forall i: int :: 0 <= i && i < tabLen ==> subset(restr(setOfSeq(lin), i), tabvis[i]))
  && (forall i: int :: 0 <= i && i < tabLen ==> subset(tabvis[i], setOfSeq(lin)))
  // Invariants needed to show monotonicity
  && (forall n1, n2 : Invoc :: called[n1] && hb(n2, n1) ==> returned[n2])
  && (forall n1, n2 : Invoc :: elem(n2, vis[n1]) ==> elem(n2, tabvis[invoc_k(n2)]))
  && (forall n1, n2 : Invoc :: elem(n2, vis[n1]) ==> 0 <= invoc_k(n2) && invoc_k(n2) < tabLen)
  // TODO The linearization is consistent with happens-before
}

function {:inline} thisInv(called: [Invoc]bool, returned: [Invoc]bool, this: Invoc) : bool
{
  called[this] && !returned[this]
}

// ---------- Primitives/helpers for modifying global state

// Write to the table
procedure {:atomic} {:layer 1} writeTable_spec(k, v: int)
  modifies table;
{
  table[k] := v;
}
procedure {:yields} {:layer 0} {:refines "writeTable_spec"}
  writeTable(k, v: int);

// Read from the table
procedure {:atomic} {:layer 1} readTable_spec(k: int)
  returns (v: int)
{
  v := table[k];
}
procedure {:yields} {:layer 0} {:refines "readTable_spec"} readTable(k: int)
  returns (v: int);


// Introduction actions:

procedure {:layer 1} intro_add_tabvis(k: int, n: Invoc)
  // TODO why don't these follow from the body?
  ensures {:layer 1} tabvis == old(tabvis)[k := add(old(tabvis)[k], n)];
  modifies tabvis;
{
  tabvis[k] := add(tabvis[k], n);
}

procedure {:layer 1} intro_read_all_tabvis() returns (s: SetInvoc);
  ensures {:layer 1} s == unionRange(tabvis, 0, tabLen);
  // TODO show these
  ensures {:layer 1} (forall n1: Invoc :: elem(n1, s) ==> elem(n1, tabvis[invoc_k(n1)]));
  ensures {:layer 1} (forall n1: Invoc :: elem(n1, s) ==> 0 <= invoc_k(n1) && invoc_k(n1) < tabLen);

procedure {:layer 1} intro_read_tabvis(s: SetInvoc, k: int) returns (t: SetInvoc);
  requires {:layer 1} (forall n1: Invoc :: elem(n1, s) ==> elem(n1, tabvis[invoc_k(n1)]));
  requires {:layer 1} (forall n1 : Invoc :: elem(n1, s) ==> 0 <= invoc_k(n1) && invoc_k(n1) < tabLen);
  ensures {:layer 1} t == union(s, tabvis[k]);
  // TODO show these
  ensures {:layer 1} (forall n1: Invoc :: elem(n1, t) ==> elem(n1, tabvis[invoc_k(n1)]));
  ensures {:layer 1} (forall n1 : Invoc :: elem(n1, t) ==> 0 <= invoc_k(n1) && invoc_k(n1) < tabLen);

procedure {:layer 1} intro_write_vis(n: Invoc, s: SetInvoc)
  modifies vis;
  ensures {:layer 1} vis == old(vis)[n := s];
{
  vis[n] := s;
}

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

procedure {:atomic} {:layer 1} spec_call_spec(m: Method, k, v: int)
  returns ({:linear "this"} this: Invoc)
  modifies called, returned;
{
  assume m == invoc_m(this) && k == invoc_k(this) && v == invoc_v(this);
  // everything before this has returned
  assume (forall n1: Invoc :: hb(n1, this) ==> returned[n1]);
  // everything after this has not been called
  assume (forall n1: Invoc :: hb(this, n1) ==> !called[n1]);
  // this has not been called or returned yet
  assume (!called[this] && !returned[this]);
  called[this] := true;
}
procedure {:yields} {:layer 0} {:refines "spec_call_spec"}
  spec_call(m: Method, k, v: int) returns ({:linear "this"} this: Invoc);

procedure {:atomic} {:layer 1} spec_return_spec({:linear "this"} this: Invoc)
  modifies returned;
{
  returned[this] := true;
}
procedure {:yields} {:layer 0} {:refines "spec_return_spec"}
  spec_return({:linear "this"} this: Invoc);


// ---------- Introduction actions used to encode assume statements -- prove these

// TODO true because tabvis[k] only affects state of k
// Problem: how to say (t affects only k) ==> state(union(s, t))[i != k] == state(s)[i]
// without quantifier alternation?
procedure {:layer 1} lemma_state_unchanged(k: int, old_vis, new_vis: SetInvoc);
  requires new_vis == union(old_vis, tabvis[k]) && 0 <= k && k < tabLen;
  ensures (forall i: int :: 0 <= i && i < k ==> state(new_vis, lin)[i] == state(old_vis, lin)[i]);

// ---------- The ADT methods

procedure {:atomic} {:layer 2} put_spec(k: int, v: int)
  modifies abs, lin, vis;
{
  var {:linear "this"} this: Invoc;
  var my_vis: SetInvoc;
  assume put == invoc_m(this) && k == invoc_k(this) && v == invoc_v(this);
  lin := append(lin, this);
  vis[this] := my_vis;
  // Put is complete
  assume my_vis == setOfSeq(lin);

  // Put satisfies its functional spec
  abs[k] := v;
}

procedure {:yields} {:layer 1} {:refines "put_spec"} put(k, v: int)
  requires {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  requires {:layer 1} 0 <= k && k < tabLen;
  ensures {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
{
  var {:linear "this"} this: Invoc;
  var {:layer 1} my_vis: SetInvoc;
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  call this := spec_call(put, k, v);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && thisInv(called, returned, this);

  call writeTable(k, v);

  call intro_add_tabvis(k, this);
  call my_vis := intro_read_all_tabvis();
  call intro_write_vis(this, my_vis);
  call intro_writeAbs(k, v);
  call intro_writeLin(this);

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
    && thisInv(called, returned, this);
  call spec_return(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
}


procedure {:atomic} {:layer 2} get_spec(k: int) returns (v: int)
  modifies lin, vis;
{
  var {:linear "this"} this: Invoc; var my_vis: SetInvoc;
  assume get == invoc_m(this) && k == invoc_k(this);
  lin := append(lin, this);
  vis[this] := my_vis;
  // Get is complete -- TODO make predicate
  assume my_vis == setOfSeq(lin);

  // Get satisfies its functional spec
  v := abs[k];
}

procedure {:yields} {:layer 1} {:refines "get_spec"} get(k: int)
  returns (v: int)
  requires {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  requires {:layer 1} 0 <= k && k < tabLen;
  ensures {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
{
  var {:linear "this"} this: Invoc;
  var {:layer 1} my_vis: SetInvoc;
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  call this := spec_call(get, k, v);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && thisInv(called, returned, this);

  call v := readTable(k);

  call intro_add_tabvis(k, this);
  call my_vis := intro_read_all_tabvis();
  call intro_write_vis(this, my_vis);
  call intro_writeLin(this);

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
  && thisInv(called, returned, this);
  call spec_return(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
}


procedure {:atomic} {:layer 2} test_spec()
  modifies vis;
{
  var {:linear "this"} this: Invoc;
  var my_vis: SetInvoc;
  assume contains == invoc_m(this) && 0 == invoc_k(this) && 0 == invoc_v(this);
  vis[this] := my_vis;
  // test is monotonic
  assume (forall j: Invoc :: hb(j, this) ==> subset(vis[j], my_vis));
}

procedure {:yields} {:layer 1} {:refines "test_spec"} test()
  modifies vis;
  requires {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  ensures {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
{
  var k, tv: int;
  var {:linear "this"} this: Invoc;
  var old_vis: SetInvoc; var old_tabvis: [int]SetInvoc;
  var {:layer 1} my_vis: SetInvoc;
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  call this := spec_call(contains, 0, 0);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && thisInv(called, returned, this);

  k := 0;
  my_vis := emptySet;

  while (k < tabLen)
    invariant {:layer 1} 0 <= k && k <= tabLen;
    invariant {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && thisInv(called, returned, this);
    invariant {:layer 1} (forall n1 : Invoc :: elem(n1, my_vis) ==> elem(n1, tabvis[invoc_k(n1)]));
    invariant {:layer 1} (forall n1 : Invoc :: elem(n1, my_vis) ==> 0 <= invoc_k(n1) && invoc_k(n1) < tabLen);
    invariant {:layer 1} (forall n1, n2: Invoc ::
                          hb(n1, this) && elem(n2, vis[n1])
                          && 0 <= invoc_k(n2) && invoc_k(n2) < k
                          ==> elem(n2, my_vis));
  {
    // Read table[k] and add tabvis[k] to my_vis
    call tv := readTable(k);
    call my_vis := intro_read_tabvis(my_vis, k);
    k := k + 1;
    yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
      && thisInv(called, returned, this)
      && (forall n1 : Invoc :: elem(n1, my_vis) ==> elem(n1, tabvis[invoc_k(n1)]))
      && (forall n1 : Invoc :: elem(n1, my_vis) ==> 0 <= invoc_k(n1) && invoc_k(n1) < tabLen)
      && (forall n1, n2: Invoc :: hb(n1, this) && elem(n2, vis[n1])
         && 0 <= invoc_k(n2) && invoc_k(n2) < k ==> elem(n2, my_vis));
  }
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && thisInv(called, returned, this)
    && (forall n1 : Invoc :: elem(n1, my_vis) ==> elem(n1, tabvis[invoc_k(n1)]))
    && (forall n1 : Invoc :: elem(n1, my_vis) ==> 0 <= invoc_k(n1) && invoc_k(n1) < tabLen)
    && (forall n1, n2: Invoc ::
                          hb(n1, this) && elem(n2, vis[n1])
                          && 0 <= invoc_k(n2) && invoc_k(n2) < k
                          ==> elem(n2, my_vis));
  call intro_write_vis(this, my_vis);

  assert {:layer 1} (forall n1, n2 : Invoc :: elem(n2, vis[n1]) ==> 0 <= invoc_k(n2) && invoc_k(n2) < tabLen);

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && thisInv(called, returned, this);
  call spec_return(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  return;
}


/*

function contains_func_spec(vis: SetInvoc, lin: SeqInvoc, witness_k: int,
                            v: int, res: bool) : bool
{
   (res ==> state(vis, lin)[witness_k] == v)
   && (!res ==> (forall i: int :: 0 <= i && i < tabLen ==> state(vis, lin)[i] != v))
}

procedure {:atomic} {:layer 2} contains_spec(v: int)
  returns (res: bool, my_vis: SetInvoc, witness_k: int)
  modifies lin, vis;
{
  var {:linear "this"} this: Invoc;
  assume contains == invoc_m(this) && witness_k == invoc_k(this) && v == invoc_v(this);
  lin := append(lin, this);
  vis := vis[this := my_vis];
  // Contains is monotonic
  assume (forall j: Invoc :: hb(j, this) ==> subset(vis[j], my_vis));

  // Contains satisfies its functional spec
  assume contains_func_spec(my_vis, lin, witness_k, v, res);
}

procedure {:yields} {:layer 1} {:refines "contains_spec"} contains(v: int)
  returns (res: bool, my_vis: SetInvoc, witness_k: int)
  requires {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  ensures {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
{
  var k, tv: int;
  var {:linear "this"} this: Invoc;
  var old_vis: SetInvoc;
  var old_tabvis: [int]SetInvoc; var {:layer 1} old_lin: SeqInvoc;

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  call this := spec_call(contains, tabLen-1, v);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && thisInv(called, returned, this);
  k := 0;
  my_vis := emptySet;
  while (k < tabLen)
    invariant {:layer 1} 0 <= k && k <= tabLen;
    invariant {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && thisInv(called, returned, this);
    invariant {:layer 1} (forall i: int :: 0 <= i && i < k ==> state(my_vis, lin)[i] != v);
    invariant {:layer 1} subset(my_vis, setOfSeq(lin));
    invariant {:layer 1} (forall n1, n2: Invoc ::
                          hb(n1, this) && elem(n2, vis[n1])
                          && 0 <= invoc_k(n2) && invoc_k(n2) < k
                          ==> elem(n2, my_vis));
  {
    // Read table[k] and add tabvis[k] to my_vis
    call tv, old_vis, my_vis := readTable1(k, my_vis);
    call lemma_state_unchanged(k, old_vis, my_vis);

    // tv == table[k] == abs[k] == state(tabvis[k], lin)[k]
    // old_vis < setOfSeq(lin) ==> restr(old_vis, k) < restr(setOfSeq(lin), k)
    assert {:layer 1} subset(restr(old_vis, k), restr(setOfSeq(lin), k));
    // linInv() ==> restr(setOfSeq(lin), k) < tabvis[k]
    // axiom ==> restr(my_vis, k) == restr(tabvis[k], k)
    assert {:layer 1} state(restr(my_vis, k), lin)[k]
                        == state(restr(tabvis[k], k), lin)[k];
    // == tv
    yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && thisInv(called, returned, this) && tv == state(my_vis, lin)[k]
      && (forall i: int :: 0 <= i && i < k ==> state(my_vis, lin)[i] != v)
      && subset(my_vis, setOfSeq(lin))
      && (forall n1, n2: Invoc :: hb(n1, this) && elem(n2, vis[n1])
         && 0 <= invoc_k(n2) && invoc_k(n2) < k ==> elem(n2, my_vis));

    if (tv == v) {
      // Linearization point
      my_vis := add(my_vis, this);
      witness_k := k;
      call old_tabvis := addVis(this, my_vis);
      call old_lin := intro_writeLin1(this);

      res := true;

      yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && thisInv(called, returned, this);
      return;  // TODO need to pick up rest of tabvis, transfer invariants from test
    }
    yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && thisInv(called, returned, this)
      && (forall i: int :: 0 <= i && i <= k ==> state(my_vis, lin)[i] != v)
      && subset(my_vis, setOfSeq(lin))
      && (forall n1, n2: Invoc :: hb(n1, this) && elem(n2, vis[n1])
         && 0 <= invoc_k(n2) && invoc_k(n2) < k ==> elem(n2, my_vis));

    k := k + 1;
  }
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && thisInv(called, returned, this)
    && (forall i: int :: 0 <= i && i < tabLen ==> state(my_vis, lin)[i] != v);

  // Linearization point
  old_vis := my_vis;
  my_vis := add(my_vis, this);
  witness_k := k;
  call old_tabvis := addVis(this, my_vis);
  call old_lin := intro_writeLin1(this);

  res := false;

  // TODO adding this causes divergence. Investigate
  // assert {:layer 1} (forall i: int :: 0 <= i && i < k ==>
  //                      restr(setOfSeq(lin), i) == restr(setOfSeq(old_lin), i)
  //                      && tabvis[i] == add(old_tabvis[i], this));
  assert {:layer 1} lin == append(old_lin, this) && my_vis == add(old_vis, this)
    && (forall i: int :: 0 <= i && i < tabLen ==> state(my_vis, lin)[i] == state(old_vis, old_lin)[i]);

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && thisInv(called, returned, this);
  call spec_return(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  return;
}



*/
