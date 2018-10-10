// ----------------------------------------
// A simplified hash table implementation with weakly consistent contains method
// The hash function is identity, so this is essentially a concurrent array
// ----------------------------------------


// ---------- Types of methods and invocations

type Method;

type Invoc;

// Boilerplate stuff for linear variables
function {:builtin "MapConst"} MapConstBool(bool) : [Invoc]bool;
function {:inline} {:linear "this"} TidCollector(x: Invoc) : [Invoc]bool
{
  MapConstBool(false)[x := true]
}


// ---------- Types and axiomatization of sequences (of invocations)

// Sequences of invocations
type SeqInvoc;

function Seq_append(s: SeqInvoc, o: Invoc) returns (t: SeqInvoc);

function Seq_elem(n: Invoc, s: SeqInvoc) : bool;

// Relationship between elem and append
axiom (forall n1, n2: Invoc, s: SeqInvoc :: {Seq_elem(n1, Seq_append(s, n2))}
       Seq_elem(n1, s) ==> Seq_elem(n1, Seq_append(s, n2)));

axiom (forall n: Invoc, s: SeqInvoc :: {Seq_elem(n, Seq_append(s, n))}
       Seq_elem(n, Seq_append(s, n)));


// ---------- Types and axiomatization of sets (of invocations)

// Sets of invocations
type SetInvoc;
const Set_empty: SetInvoc;

function Set_elem(n: Invoc, s: SetInvoc) : bool;

function Set_subset(s: SetInvoc, t: SetInvoc) : bool;

// Set_empty is a subset of anything
axiom (forall s: SetInvoc :: Set_subset(Set_empty, s));

// Nothing is an elem of Set_empty
axiom (forall n: Invoc :: !Set_elem(n, Set_empty));

// subset is reflexive
axiom (forall s: SetInvoc :: Set_subset(s, s));

// subset is transitive
axiom (forall s, t, u: SetInvoc :: Set_subset(s, t) && Set_subset(t, u) ==> Set_subset(s, u));

// definition of subset in terms of elem
axiom (forall s, t: SetInvoc :: (forall n: Invoc :: Set_elem(n, s) ==> Set_elem(n, t)) ==> Set_subset(s, t));

function Set_union(s1: SetInvoc, s2: SetInvoc) returns (t: SetInvoc);

// union is idempotent
axiom (forall s: SetInvoc :: s == Set_union(s, s));

// union is associative
axiom (forall s, t: SetInvoc :: Set_union(s, t) == Set_union(t, s));

// union is monotonic w.r.t subset
axiom (forall s, t1, t2: SetInvoc :: Set_subset(t1, t2) ==> Set_subset(Set_union(s, t1), Set_union(s, t2)));

axiom (forall s, t1, t2: SetInvoc :: Set_subset(t1, s) && Set_subset(t2, s) ==> Set_subset(Set_union(t1, t2), s));

// relation between union and elem
axiom (forall n: Invoc, s, s1, t: SetInvoc :: Set_elem(n, s) && s1 == Set_union(s, t) ==> Set_elem(n, s1));

// Calculate the union m[i] \cup ... \cup m[j-1]
function unionRange(m: [int]SetInvoc, i: int, j: int) returns (s: SetInvoc);

function Set_ofSeq(q: SeqInvoc) returns (s: SetInvoc);

function Set_add(s: SetInvoc, n: Invoc) returns (t: SetInvoc);

// Relation between add and elem
axiom (forall s: SetInvoc, n1, n2: Invoc :: Set_elem(n1, Set_add(s, n2))
       ==> n1 == n2 || Set_elem(n1, s));
axiom (forall s: SetInvoc, n1, n2: Invoc :: Set_elem(n1, s) ==> Set_elem(n1, Set_add(s, n2)));

// Relation between union and elem
axiom (forall s, t: SetInvoc, n1: Invoc :: Set_elem(n1, Set_union(s, t))
       ==> Set_elem(n1, s) || Set_elem(n1, t));

// add preserves subset relation
axiom (forall s, t: SetInvoc, n: Invoc :: Set_subset(s, t) ==> Set_subset(Set_add(s, n), Set_add(t, n)));
axiom (forall s, t: SetInvoc, n: Invoc :: Set_subset(s, t) ==> Set_subset(s, Set_add(t, n)));

// Relation between setOfSeq, add, and append
axiom (forall q: SeqInvoc, n: Invoc :: Set_ofSeq(Seq_append(q, n)) == Set_add(Set_ofSeq(q), n));

// Relation between unionRange, add, and append
axiom (forall t: [int]SetInvoc, i, j, k: int, q: SeqInvoc, n: Invoc ::
        unionRange(t, i, j) == Set_ofSeq(q) && i <= k && k < j
        ==> unionRange(t[k := Set_add(t[k], n)], i, j) == Set_ofSeq(Seq_append(q, n)));

// Add n to m[i], ..., m[j-1]
function addRange(m: [int]SetInvoc, n: Invoc, i: int, j: int)
  returns (m1: [int]SetInvoc);

// The effect of addRange
axiom (forall m, m1: [int]SetInvoc, n: Invoc, i: int, j: int, k: int ::
        m1 == addRange(m, n, i, j) && i <= k && k < j
        ==> m1[k] == Set_add(m[k], n));
axiom (forall m, m1: [int]SetInvoc, n: Invoc, i: int, j: int, k: int ::
        m1 == addRange(m, n, i, j) && !(i <= k && k < j)
        ==> m1[k] == m[k]);

// What happens to unionRange and setOfSeq when you do an addRange
axiom (forall t: [int]SetInvoc, i, j, i1, j1: int, q: SeqInvoc, n: Invoc ::
        unionRange(t, i, j) == Set_ofSeq(q) && i <= i1 && i1 < j1 && j1 <= j ==>
          unionRange(addRange(t, n, i1, j1), i, j) == Set_ofSeq(Seq_append(q, n)));


// ---------- Axioms of the map ADT

const unique get, put, contains: Method;

function invoc_m(n: Invoc) : Method;
function invoc_k(n: Invoc) : int;
function invoc_v(n: Invoc) : int;

// A function to restrict a SetInvoc to invocations involving key k
function restr(s: SetInvoc, k: int) returns (t: SetInvoc);

// restr is a subset
axiom (forall s: SetInvoc, k: int :: Set_subset(restr(s, k), s));

// restr is monotonic w.r.t subset
axiom (forall s, t: SetInvoc, k: int :: Set_subset(s, t) ==> Set_subset(restr(s, k), restr(t, k)));

// Adding an invocation on k increases restr
axiom (forall q: SeqInvoc, n: Invoc :: {restr(Set_ofSeq(Seq_append(q, n)), invoc_k(n))}
        restr(Set_ofSeq(Seq_append(q, n)), invoc_k(n))
          == Set_add(restr(Set_ofSeq(q), invoc_k(n)), n));

// Adding invocations not on k preserves restr
axiom (forall q: SeqInvoc, n: Invoc, k: int :: invoc_k(n) != k
       ==> restr(Set_ofSeq(Seq_append(q, n)), k) == restr(Set_ofSeq(q), k));

type AbsState = [int]int; // Abstract state

// A function to calculate the abstract state after executing a subset vis of
// a sequence of invocations lin
function state(vis: SetInvoc, lin: SeqInvoc) returns (m: AbsState);


// The effect of appending an invocation on key k on state of k
axiom (forall s1, s2: SetInvoc, q1, q2: SeqInvoc, n: Invoc ::
       q2 == Seq_append(q1, n) && s2 == Set_add(s1, n)
       ==> (invoc_m(n) == put ==> state(s2, q2)[invoc_k(n)] == invoc_v(n)));

// Appending a get/contains invocation does not change state
axiom (forall s1, s2: SetInvoc, q1, q2: SeqInvoc, n: Invoc, k: int ::
       q2 == Seq_append(q1, n) && s2 == Set_add(s1, n)
       && (invoc_m(n) == get || invoc_m(n) == contains)
       ==> state(s2, q2)[k] == state(s1, q1)[k]);

// The effect of appending an invocation on key k on state with unchanged vis
axiom (forall s: SetInvoc, q1: SeqInvoc, n: Invoc, k: int ::
          state(s, q1)[k] == state(s, Seq_append(q1, n))[k]);


// The mapping of key k depends only invocations involving k
axiom (forall s: SetInvoc, q: SeqInvoc, k: int ::
        state(s, q)[k] == state(restr(s, k), q)[k]);
axiom (forall q: SeqInvoc, k: int ::
        state(Set_ofSeq(q), q)[k] == state(restr(Set_ofSeq(q), k), q)[k]);

// Taking union with a restriction of a super-set means restrictions are same
axiom (forall s0, s1, t: SetInvoc, k: int ::
        s1 == Set_union(s0, t) && Set_subset(restr(s0, k), t) ==>
          restr(s1, k) == restr(t, k)
);

// Union of disjoint keys means state comes from one of the two sets
procedure {:layer 1} lemma_state_Set_union(k: int, s, t: SetInvoc);
  requires (forall n: Invoc :: Set_elem(n, s) ==> invoc_k(n) < k);
  requires (forall n: Invoc :: Set_elem(n, t) ==> k <= invoc_k(n));
  ensures (forall i: int :: 0 <= i && i < k ==>
    state(Set_union(s, t), lin)[i] == state(s, lin)[i]);
  ensures (forall i: int :: k <= i && i < tabLen ==>
    state(Set_union(s, t), lin)[i] == state(t, lin)[i]);


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
  && unionRange(tabvis, 0, tabLen) == Set_ofSeq(lin)
  && (forall i: int :: 0 <= i && i < tabLen ==> state(tabvis[i], lin)[i] == abs[i])
  && (forall i: int :: 0 <= i && i < tabLen ==>
      state(tabvis[i], lin)[i] == state(restr(Set_ofSeq(lin), i), lin)[i])
  && (forall i: int :: 0 <= i && i < tabLen ==> Set_subset(restr(Set_ofSeq(lin), i), tabvis[i]))
  && (forall i: int :: 0 <= i && i < tabLen ==> Set_subset(tabvis[i], Set_ofSeq(lin)))
  && (forall i: int, n: Invoc :: 0 <= i && i < tabLen && Set_elem(n, tabvis[i])
      ==> invoc_k(n) == i)
  // Used to infer that invocations don't modify vis after they've returned
  && (forall n1, n2 : Invoc :: called[n1] && hb(n2, n1) ==> returned[n2])
  // Sanity conditions on vis sets
  && (forall n1, n2 : Invoc :: Set_elem(n2, vis[n1]) ==> Set_elem(n2, tabvis[invoc_k(n2)]))
  && (forall n1, n2 : Invoc :: Set_elem(n2, vis[n1]) ==> 0 <= invoc_k(n2) && invoc_k(n2) < tabLen)
  // To establish precondition of intro_writeLin
  && (forall n: Invoc :: returned[n] ==> Seq_elem(n, lin))
}

function {:inline} inProgress(called: [Invoc]bool, returned: [Invoc]bool, this: Invoc) : bool
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


// ---------- Introduction actions:

procedure {:layer 1} intro_add_tabvis(k: int, n: Invoc)
  // TODO why don't these follow from the body?
  ensures {:layer 1} tabvis == old(tabvis)[k := Set_add(old(tabvis)[k], n)];
  modifies tabvis;
{
  tabvis[k] := Set_add(tabvis[k], n);
}

procedure {:layer 1} intro_read_tabvis_range(i, j: int) returns (s: SetInvoc);
  ensures {:layer 1} s == unionRange(tabvis, i, j);
  ensures {:layer 1} (forall n: Invoc, k: int :: Set_elem(n, tabvis[k]) && i <= k && k < j ==> Set_elem(n, s));
  // TODO show these
  ensures {:layer 1} (forall n1: Invoc :: Set_elem(n1, s) ==> Set_elem(n1, tabvis[invoc_k(n1)]));
  ensures {:layer 1} (forall n1: Invoc :: Set_elem(n1, s)
    ==> i <= invoc_k(n1) && invoc_k(n1) < j);

procedure {:layer 1} intro_read_tabvis(k: int) returns (s: SetInvoc)
  ensures {:layer 1} s == tabvis[k];
{
  s := tabvis[k];
}

procedure {:layer 1} intro_write_vis(n: Invoc, s: SetInvoc)
  modifies vis;
  ensures {:layer 1} vis == old(vis)[n := s];
{
  vis[n] := s;
}

procedure {:layer 1} {:inline 1} intro_writeLin(n: Invoc)
  // To show that linearization is consistent with happens-before
  requires {:layer 1} (forall n1 : Invoc :: hb(n1, n) ==> Seq_elem(n1, lin));
  modifies lin;
{
  lin := Seq_append(lin, n);
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


// ---------- The ADT methods

procedure {:atomic} {:layer 2} put_spec(k: int, v: int)
  modifies abs, lin, vis;
{
  var {:linear "this"} this: Invoc;
  var my_vis: SetInvoc;
  assume put == invoc_m(this) && k == invoc_k(this) && v == invoc_v(this);
  lin := Seq_append(lin, this);
  vis[this] := my_vis;
  // Put is complete
  assume my_vis == Set_ofSeq(lin);

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
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && inProgress(called, returned, this);

  call writeTable(k, v);

  call intro_add_tabvis(k, this);
  call my_vis := intro_read_tabvis_range(0, tabLen);
  call intro_write_vis(this, my_vis);
  call intro_writeAbs(k, v);
  call intro_writeLin(this);

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
    && inProgress(called, returned, this) && Seq_elem(this, lin);
  call spec_return(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
}


procedure {:atomic} {:layer 2} get_spec(k: int) returns (v: int)
  modifies lin, vis;
{
  var {:linear "this"} this: Invoc; var my_vis: SetInvoc;
  assume get == invoc_m(this) && k == invoc_k(this);
  lin := Seq_append(lin, this);
  vis[this] := my_vis;
  // Get is complete -- TODO make predicate
  assume my_vis == Set_ofSeq(lin);

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
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && inProgress(called, returned, this);

  call v := readTable(k);

  call intro_add_tabvis(k, this);
  call my_vis := intro_read_tabvis_range(0, tabLen);
  call intro_write_vis(this, my_vis);
  call intro_writeLin(this);

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
    && inProgress(called, returned, this) && Seq_elem(this, lin);
  call spec_return(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
}


function contains_func_spec(vis: SetInvoc, lin: SeqInvoc, witness_k: int,
                            v: int, res: bool) : bool
{
   (res ==> state(vis, lin)[witness_k] == v)
   && (!res ==> (forall i: int :: 0 <= i && i < tabLen ==> state(vis, lin)[i] != v))
}

procedure {:atomic} {:layer 2} contains_spec(v: int)
  returns (res: bool, witness_k: int)
  modifies lin, vis;
{
  var {:linear "this"} this: Invoc;
  var my_vis: SetInvoc;
  assume contains == invoc_m(this) && tabLen-1 == invoc_k(this) && v == invoc_v(this);
  lin := Seq_append(lin, this);
  vis[this] := my_vis;
  // Contains is monotonic
  assume (forall j: Invoc :: hb(j, this) ==> Set_subset(vis[j], my_vis));

  // Contains satisfies its functional spec
  assume contains_func_spec(my_vis, lin, witness_k, v, res);
}

procedure {:yields} {:layer 1} {:refines "contains_spec"} contains(v: int)
  returns (res: bool, witness_k: int)
  requires {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  ensures {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
{
  var k, tv: int;
  var {:linear "this"} this: Invoc;
  var {:layer 1} my_vis, my_vis1: SetInvoc;
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  call this := spec_call(contains, tabLen-1, v);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && inProgress(called, returned, this);

  k := 0;
  my_vis := Set_empty;

  while (k < tabLen)
    invariant {:layer 1} 0 <= k && k <= tabLen;
    invariant {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && inProgress(called, returned, this);
    invariant {:layer 1} (forall i: int :: 0 <= i && i < k ==> state(my_vis, lin)[i] != v);
    invariant {:layer 1} Set_subset(my_vis, Set_ofSeq(lin));
    invariant {:layer 1} (forall n1 : Invoc :: Set_elem(n1, my_vis) ==> Set_elem(n1, tabvis[invoc_k(n1)]));
    invariant {:layer 1} (forall n1 : Invoc :: Set_elem(n1, my_vis) ==> 0 <= invoc_k(n1) && invoc_k(n1) < k);
    invariant {:layer 1} (forall n1, n2: Invoc ::
                          hb(n1, this) && Set_elem(n2, vis[n1])
                          && 0 <= invoc_k(n2) && invoc_k(n2) < k
                          ==> Set_elem(n2, my_vis));
  {
    // Read table[k] and add tabvis[k] to my_vis
    call tv := readTable(k);

    call my_vis1 := intro_read_tabvis(k);
    call lemma_state_Set_union(k, my_vis, my_vis1);
    my_vis := Set_union(my_vis, my_vis1);

    if (tv == v) {
      // Linearization point
      call my_vis1 := intro_read_tabvis_range(k+1, tabLen);
      assert {:layer 1} (forall n1, n2: Invoc ::
                          hb(n1, this) && Set_elem(n2, vis[n1])
                          && 0 <= invoc_k(n2) && invoc_k(n2) < k+1
                          ==> Set_elem(n2, my_vis));
      call lemma_state_Set_union(k+1, my_vis, my_vis1);
      my_vis := Set_union(my_vis, my_vis1);
      call intro_write_vis(this, my_vis);
      call intro_add_tabvis(tabLen-1, this);
      call intro_writeLin(this);
      witness_k := k;

      res := true;

      yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
        && inProgress(called, returned, this) && Seq_elem(this, lin);
      call spec_return(this);
      yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
      return;
    }
    k := k + 1;
    yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && inProgress(called, returned, this)
      && (forall i: int :: 0 <= i && i < k ==> state(my_vis, lin)[i] != v)
      && Set_subset(my_vis, Set_ofSeq(lin))
      && (forall n1 : Invoc :: Set_elem(n1, my_vis) ==> Set_elem(n1, tabvis[invoc_k(n1)]))
      && (forall n1 : Invoc :: Set_elem(n1, my_vis) ==> 0 <= invoc_k(n1) && invoc_k(n1) < k);
      assert {:layer 1} (forall n1, n2: Invoc :: hb(n1, this) && Set_elem(n2, vis[n1])
         && 0 <= invoc_k(n2) && invoc_k(n2) < k ==> Set_elem(n2, my_vis));
  }
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && inProgress(called, returned, this)
    && (forall i: int :: 0 <= i && i < tabLen ==> state(my_vis, lin)[i] != v)
    && (forall n1 : Invoc :: Set_elem(n1, my_vis) ==> Set_elem(n1, tabvis[invoc_k(n1)]))
    && (forall n1 : Invoc :: Set_elem(n1, my_vis) ==> 0 <= invoc_k(n1) && invoc_k(n1) < tabLen)
    && (forall n1, n2: Invoc :: hb(n1, this) && Set_elem(n2, vis[n1])
                         && 0 <= invoc_k(n2) && invoc_k(n2) < k
                         ==> Set_elem(n2, my_vis));

  // Linearization point
  call intro_write_vis(this, my_vis);
  call intro_add_tabvis(tabLen-1, this);
  call intro_writeLin(this);
  witness_k := k;

  res := false;

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
    && inProgress(called, returned, this) && Seq_elem(this, lin);
  call spec_return(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  return;
}
