// ----------------------------------------
// A simplified hash table implementation with weakly consistent contains method
// The hash function is identity, so this is essentially a concurrent array
// ----------------------------------------


// ---------- Types and axiomatization of sequences (of invocations)

// Sequences of invocations
type SeqInvoc;

function Seq_append(s: SeqInvoc, o: Invoc) returns (t: SeqInvoc);

function Seq_elem(n: Invoc, s: SeqInvoc) : bool;

// Relationship between elem and append
axiom (forall n1, n2: Invoc, s: SeqInvoc :: {Seq_elem(n1, Seq_append(s, n2))}
       Seq_elem(n1, Seq_append(s, n2)) <==> Seq_elem(n1, s) || n1 == n2);


// ---------- Types and axiomatization of sets (of invocations)  // TODO unify

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
axiom (forall s, t: SetInvoc ::
  (forall n: Invoc :: Set_elem(n, s) ==> Set_elem(n, t))
  <==> Set_subset(s, t));

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

// Calculate the union m[i] \cup ... \cup m[j-1]
function unionRange(m: [int]SetInvoc, i: int, j: int) returns (s: SetInvoc);

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
axiom (forall s, t: SetInvoc, n1: Invoc :: Set_elem(n1, Set_union(s, t))
       ==> Set_elem(n1, s) || Set_elem(n1, t));

// add preserves subset relation
axiom (forall s, t: SetInvoc, n: Invoc :: Set_subset(s, t) ==> Set_subset(Set_add(s, n), Set_add(t, n)));
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

axiom (forall q: SeqInvoc, s: SetInvoc, n: Invoc ::
    {Seq_restr(Seq_append(q, n), Set_add(s, n))}
  Seq_distinct(Seq_append(q, n)) && !Set_elem(n, s)
  ==> Seq_restr(Seq_append(q, n), Set_add(s, n)) == Seq_append(Seq_restr(q, s), n));

// Relation between Seq_elem and Seq_restr
axiom (forall q: SeqInvoc, s: SetInvoc, n: Invoc :: {Seq_elem(n, Seq_restr(q, s))}
  Seq_elem(n, Seq_restr(q, s)) <==> Seq_elem(n, q) && Set_elem(n, s));


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


// ---------- Types of methods and invocations

type Method;

type Invoc;

// Boilerplate stuff for linear variables
function {:builtin "MapConst"} MapConstInvocBool(bool) : [Invoc]bool;
function {:inline} {:linear "this"} TidCollector(x: Invoc) : [Invoc]bool
{
  MapConstInvocBool(false)[x := true]
}


// ---------- Representation of execution and linearization

// hb(x, y) : x happens-before y.  // TODO make var, have actions to add these
// We assume there exists such a function, given by the client program
function hb(x: Invoc, y: Invoc) : bool;
axiom (forall n: Invoc :: !hb(n, n));

// A shared global variable that builds the linearization
var {:layer 1,2} lin: SeqInvoc;

// A map from invocations to the set of prior invocations visible to them
var {:layer 1,2} vis: [Invoc]SetInvoc;

// The map from invocations to method and argument values is encoded in the Invoc type
// so as to not further complicate the Queue ADT axioms above
// The map from invocations to return values is implicitly stored in the ghost vars
// retK & retS. Since return values are determined at the LPs, we store them at LP time.

procedure {:layer 1} intro_readLin() returns (s: SetInvoc)
  ensures {:layer 1} s == Set_ofSeq(lin);
{
  s := Set_ofSeq(lin);
}

procedure {:layer 1} intro_writeVis(n: Invoc, s: SetInvoc)
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


// ---------- Axioms of the map ADT

const unique Map.get, Map.put, Map.contains: Method;

function invoc_m(n: Invoc) : Method;
function invoc_k(n: Invoc) : int;
function invoc_v(n: Invoc) : int;

type Map.State = [int]int; // Abstract state

function Map.ofSeq(s: SeqInvoc) : Map.State;

// Effect of put to the abstract state of a Map
axiom (forall s: SeqInvoc, n: Invoc :: {Map.ofSeq(Seq_append(s, n))}
  invoc_m(n) == Map.put
  ==> Map.ofSeq(Seq_append(s, n))
    == Map.ofSeq(s)[invoc_k(n) := invoc_v(n)]);

// Effect of get/contains to the abstract state of a Map
axiom (forall s: SeqInvoc, n: Invoc :: {Map.ofSeq(Seq_append(s, n))}
  (invoc_m(n) == Map.get || invoc_m(n) == Map.contains)
  ==> Map.ofSeq(Seq_append(s, n))
    == Map.ofSeq(s));

// A function to restrict a SetInvoc to invocations involving key k
function Map.restr(s: SetInvoc, k: int) returns (t: SetInvoc);

// Map.restr is a subset
axiom (forall s: SetInvoc, k: int :: Set_subset(Map.restr(s, k), s));

// Map.restr is monotonic w.r.t subset
axiom (forall s, t: SetInvoc, k: int :: Set_subset(s, t) ==> Set_subset(Map.restr(s, k), Map.restr(t, k)));

// Adding an invocation on k increases Map.restr
axiom (forall q: SeqInvoc, n: Invoc :: {Map.restr(Set_ofSeq(Seq_append(q, n)), invoc_k(n))}
        Map.restr(Set_ofSeq(Seq_append(q, n)), invoc_k(n))
          == Set_add(Map.restr(Set_ofSeq(q), invoc_k(n)), n));

// Adding invocations not on k preserves Map.restr
axiom (forall q: SeqInvoc, n: Invoc, k: int :: invoc_k(n) != k
       ==> Map.restr(Set_ofSeq(Seq_append(q, n)), k) == Map.restr(Set_ofSeq(q), k));

// The mapping of key k depends only invocations involving k
axiom (forall s: SetInvoc, q: SeqInvoc, k: int ::
        Map.ofSeq(Seq_restr(q, s))[k] == Map.ofSeq(Seq_restr(q, Map.restr(s, k)))[k]);
axiom (forall q: SeqInvoc, k: int ::
        Map.ofSeq(Seq_restr(q, Set_ofSeq(q)))[k]
        == Map.ofSeq(Seq_restr(q, Map.restr(Set_ofSeq(q), k)))[k]);

// Taking union with a restriction of a super-set means restrictions are same
axiom (forall s0, s1, t: SetInvoc, k: int ::
        s1 == Set_union(s0, t) && Set_subset(Map.restr(s0, k), t) ==>
          Map.restr(s1, k) == Map.restr(t, k)
);

// Union of disjoint keys means state comes from one of the two sets
procedure {:layer 1} lemma_state_Set_union(k: int, s, t: SetInvoc);
  requires (forall n: Invoc :: Set_elem(n, s) ==> invoc_k(n) < k);
  requires (forall n: Invoc :: Set_elem(n, t) ==> k <= invoc_k(n));
  ensures (forall i: int :: 0 <= i && i < k ==>
    Map.ofSeq(Seq_restr(lin, Set_union(s, t)))[i] == Map.ofSeq(Seq_restr(lin, s))[i]);
  ensures (forall i: int :: k <= i && i < tabLen ==>
    Map.ofSeq(Seq_restr(lin, Set_union(s, t)))[i] == Map.ofSeq(Seq_restr(lin, t))[i]);


// ---------- Atomic specification program:

// procedure {:atomic} {:layer 2} hb_action(n1: Invoc, n2: Invoc)

procedure {:atomic} {:layer 2} put_call_atomic({:linear "this"} this: Invoc) {}

procedure {:atomic} {:layer 2} put_spec(k: int, v: int, {:linear "this"} this: Invoc)
  modifies abs, lin, vis;
{
  var my_vis: SetInvoc;

  // Satisfies its functional spec  // TODO instead, add to Inv that abs execution satisfies S
  assume true;
  abs[k] := v;

  // Is absolute
  // assume my_vis == Set_ofSeq(lin);
  my_vis := Set_ofSeq(lin);

  lin := Seq_append(lin, this);
  vis[this] := my_vis;
}

procedure {:atomic} {:layer 2} put_return_atomic({:linear "this"} this: Invoc) {}

procedure {:atomic} {:layer 2} get_call_atomic({:linear "this"} this: Invoc) {}

procedure {:atomic} {:layer 2} get_spec(k: int, {:linear "this"} this: Invoc) returns (v: int)
  modifies lin, vis;
{
  var my_vis: SetInvoc;

  // Get satisfies its functional spec
  v := abs[k];

  // Get is absolute
  // assume my_vis == Set_ofSeq(lin);
  my_vis := Set_ofSeq(lin);

  lin := Seq_append(lin, this);
  vis[this] := my_vis;
}

procedure {:atomic} {:layer 2} get_return_atomic({:linear "this"} this: Invoc) {}

procedure {:atomic} {:layer 2} contains_call_atomic({:linear "this"} this: Invoc) {}

function contains_func_spec(vis: SetInvoc, lin: SeqInvoc, witness_k: int,
                            v: int, res: bool) : bool
{
   (res ==> Map.ofSeq(Seq_restr(lin, vis))[witness_k] == v)
   && (!res ==> (forall i: int :: 0 <= i && i < tabLen
    ==> Map.ofSeq(Seq_restr(lin, vis))[i] != v))
}

procedure {:atomic} {:layer 2} contains_spec(v: int, {:linear "this"} this: Invoc)
  returns (res: bool, witness_k: int)
  modifies lin, vis;
{
  var my_vis: SetInvoc;

  // Contains satisfies its functional spec
  assume contains_func_spec(my_vis, lin, witness_k, v, res);

  // Contains is monotonic
  assume (forall j: Invoc :: hb(j, this) ==> Set_subset(vis[j], my_vis));

  lin := Seq_append(lin, this);
  vis[this] := my_vis;
}

procedure {:atomic} {:layer 2} contains_return_atomic({:linear "this"} this: Invoc) {}



// ---------- Map implementation: Shared state and invariant

// Concrete state of implementation
var {:layer 0,1} table: [int]int;
const tabLen: int;
axiom 0 < tabLen;

// Visibility per location of concrete state
var {:layer 1,1} tabvis: [int]SetInvoc;


// Abstract state of ADT  // TODO layer 1,1
var {:layer 1,2} abs: Map.State;

// The set of invocations that have been called
var {:layer 1,1} called: [Invoc]bool;

// The set of invocations that have returned
var {:layer 1,1} returned: [Invoc]bool;


function {:inline} abstracts(conc: [int]int, abs: Map.State) : bool
{
  (forall i: int :: 0 <= i && i < tabLen ==> conc[i] == abs[i])
}

// The invariants
function {:inline} tableInv(table: [int]int, abs: Map.State, tabvis: [int]SetInvoc,
                            lin: SeqInvoc, vis: [Invoc]SetInvoc, tabLen: int,
                            called: [Invoc]bool, returned: [Invoc]bool) : bool
{
  abstracts(table, abs)
  && unionRange(tabvis, 0, tabLen) == Set_ofSeq(lin)
  && (forall i: int :: 0 <= i && i < tabLen
    ==> Map.ofSeq(Seq_restr(lin, tabvis[i]))[i] == abs[i])
  && (forall i: int :: 0 <= i && i < tabLen
    ==> Map.ofSeq(Seq_restr(lin, tabvis[i]))[i]
      == Map.ofSeq(Seq_restr(lin, Map.restr(Set_ofSeq(lin), i)))[i])
  && (forall i: int :: 0 <= i && i < tabLen
    ==> Set_subset(Map.restr(Set_ofSeq(lin), i), tabvis[i]))
  && (forall i: int :: 0 <= i && i < tabLen
    ==> Set_subset(tabvis[i], Set_ofSeq(lin)))
  && (forall i: int, n: Invoc :: 0 <= i && i < tabLen && Set_elem(n, tabvis[i])
    ==> invoc_k(n) == i)
  // Sanity conditions on lin
  && (forall n2 : Invoc :: Set_elem(n2, Set_ofSeq(lin))
    ==> Set_elem(n2, tabvis[invoc_k(n2)]))
  && (forall n2 : Invoc :: Set_elem(n2, Set_ofSeq(lin))
    ==> 0 <= invoc_k(n2) && invoc_k(n2) < tabLen)
  // Sanity conditions on vis sets
  && (forall n1, n2 : Invoc :: Set_elem(n2, vis[n1])
    ==> Set_elem(n2, tabvis[invoc_k(n2)]))
  && (forall n1, n2 : Invoc :: Set_elem(n2, vis[n1])
    ==> 0 <= invoc_k(n2) && invoc_k(n2) < tabLen)
  // lin only contains called things
  && (forall n: Invoc :: {Seq_elem(n, lin)} Seq_elem(n, lin) ==> called[n])
  // lin contains distinct elements
  && Seq_distinct(lin)
  // vis sets only contain linearized ops
  && (forall n1, n2: Invoc :: {Set_elem(n1, vis[n2])}
    Set_elem(n1, vis[n2]) && returned[n2] ==> Set_elem(n1, Set_ofSeq(lin)))
  // Used to infer that invocations don't modify vis after they've returned
  && (forall n1, n2 : Invoc :: called[n1] && hb(n2, n1) ==> returned[n2])
  // To establish precondition of intro_writeLin
  && (forall n: Invoc :: returned[n] ==> Seq_elem(n, lin))
}

  /*
  assert {:layer 1} abstracts(table, abs);
  assert {:layer 1} unionRange(tabvis, 0, tabLen) == Set_ofSeq(lin);
  assert {:layer 1} (forall i: int :: 0 <= i && i < tabLen
    ==> Map.ofSeq(Seq_restr(lin, tabvis[i]))[i] == abs[i]);
  assert {:layer 1} (forall i: int :: 0 <= i && i < tabLen
    ==> Map.ofSeq(Seq_restr(lin, tabvis[i]))[i]
      == Map.ofSeq(Seq_restr(lin, Map.restr(Set_ofSeq(lin), i)))[i]);
  assert {:layer 1} (forall i: int :: 0 <= i && i < tabLen
    ==> Set_subset(Map.restr(Set_ofSeq(lin), i), tabvis[i]));
  assert {:layer 1} (forall i: int :: 0 <= i && i < tabLen
    ==> Set_subset(tabvis[i], Set_ofSeq(lin)));
  assert {:layer 1} (forall i: int, n: Invoc :: 0 <= i && i < tabLen && Set_elem(n, tabvis[i])
    ==> invoc_k(n) == i);
  // Sanity conditions on lin
  assert {:layer 1} (forall n2 : Invoc :: Set_elem(n2, Set_ofSeq(lin))
    ==> Set_elem(n2, tabvis[invoc_k(n2)]))
  assert {:layer 1} (forall n2 : Invoc :: Set_elem(n2, Set_ofSeq(lin))
    ==> 0 <= invoc_k(n2) && invoc_k(n2) < tabLen)
  // Sanity conditions on vis sets
  assert {:layer 1} (forall n1, n2 : Invoc :: Set_elem(n2, vis[n1])
    ==> Set_elem(n2, tabvis[invoc_k(n2)]));
  assert {:layer 1} (forall n1, n2 : Invoc :: Set_elem(n2, vis[n1])
    ==> 0 <= invoc_k(n2) && invoc_k(n2) < tabLen);
  // lin only contains called things
  assert {:layer 1} (forall n: Invoc :: {Seq_elem(n, lin)} Seq_elem(n, lin) ==> called[n]);
  // vis sets only contain linearized ops
  assert {:layer 1} (forall n1, n2: Invoc :: {Set_elem(n1, vis[n2])}
    Set_elem(n1, vis[n2]) && returned[n2] ==> Set_elem(n1, Set_ofSeq(lin)));
  // Used to infer that invocations don't modify vis after they've returned
  assert {:layer 1} (forall n1, n2 : Invoc :: called[n1] && hb(n2, n1) ==> returned[n2]);
  // To establish precondition of intro_writeLin
  assert {:layer 1} (forall n: Invoc :: returned[n] ==> Seq_elem(n, lin));
  */

function {:inline} preLP(called: [Invoc]bool, returned: [Invoc]bool, lin: SeqInvoc, this: Invoc) : bool
{
  called[this] && !returned[this] && !Seq_elem(this, lin)
}

function {:inline} postLP(called: [Invoc]bool, returned: [Invoc]bool, lin: SeqInvoc, this: Invoc) : bool
{
  called[this] && !returned[this] && Seq_elem(this, lin)
}


// ---------- Primitives for manipulating global state

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


// ---------- Primitives for manipulating logical/abstract state

procedure {:layer 1} intro_add_tabvis(k: int, n: Invoc)
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

procedure {:layer 1} {:inline 1} intro_writeAbs(k: int, v: int)
  modifies abs;
{
  abs[k] := v;
}

procedure {:layer 1} {:inline 1} intro_writeCalled({:linear "this"} this: Invoc)
  modifies called;
{
  called[this] := true;
}

procedure {:layer 1} {:inline 1} intro_writeReturned({:linear "this"} this: Invoc)
  modifies returned;
{
  returned[this] := true;
}


// ---------- Implementation of Map:


procedure {:yields} {:layer 1} {:refines "put_call_atomic"}
    put_call({:linear "this"} this: Invoc)
  requires {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  // everything before this has returned
  requires {:layer 1} (forall n1: Invoc :: hb(n1, this) ==> returned[n1]);
  // this has not been called or returned yet
  requires {:layer 1} (!called[this] && !returned[this]);
  ensures {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  ensures {:layer 1} preLP(called, returned, lin, this);
  modifies called;
{
  yield;
  assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  assert {:layer 1} (forall n1: Invoc :: hb(n1, this) ==> returned[n1]);
  assert {:layer 1} (!called[this] && !returned[this]);

  call intro_writeCalled(this);
  yield;
  assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  assert {:layer 1} preLP(called, returned, lin, this);
}


procedure {:yields} {:layer 1} {:refines "put_spec"} put(k, v: int, {:linear "this"} this: Invoc)
  requires {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  requires {:layer 1} preLP(called, returned, lin, this);
  requires {:layer 1} invoc_m(this) == Map.put && invoc_k(this) == k && invoc_v(this) == v;
  requires {:layer 1} 0 <= k && k < tabLen;
  ensures {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  ensures {:layer 1} postLP(called, returned, lin, this);
  ensures {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
{
  var {:layer 1} my_vis: SetInvoc;
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);

  call writeTable(k, v);

  call intro_add_tabvis(k, this);
  call my_vis := intro_readLin();
  call intro_writeLin(this);
  call intro_writeVis(this, my_vis);
  call intro_writeAbs(k, v);

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
    && postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
}

procedure {:yields} {:layer 1} {:refines "put_return_atomic"}
    put_return({:linear "this"} this: Invoc)
  requires {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  requires {:layer 1} postLP(called, returned, lin, this);
  requires {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
  ensures {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  modifies returned;
{
  yield;
  assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  assert {:layer 1} postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));

  call intro_writeReturned(this);

  yield;
  assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
}


procedure {:yields} {:layer 1} {:refines "get_spec"} get(k: int, {:linear "this"} this: Invoc)
  returns (v: int)
  requires {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  requires {:layer 1} preLP(called, returned, lin, this);
  requires {:layer 1} invoc_m(this) == Map.get && invoc_k(this) == k;
  requires {:layer 1} 0 <= k && k < tabLen;
  ensures {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  ensures {:layer 1} postLP(called, returned, lin, this);
  ensures {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
{
  var {:layer 1} my_vis: SetInvoc;
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);

  call v := readTable(k);

  call intro_add_tabvis(k, this);
  call my_vis := intro_readLin();
  call intro_writeVis(this, my_vis);
  call intro_writeLin(this);

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
    && postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
}


procedure {:yields} {:layer 1} {:refines "contains_spec"}
    contains(v: int, {:linear "this"} this: Invoc)
  returns (res: bool, witness_k: int)
  requires {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  requires {:layer 1} preLP(called, returned, lin, this);
  requires {:layer 1} invoc_m(this) == Map.contains && invoc_v(this) == v;
  ensures {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  ensures {:layer 1} postLP(called, returned, lin, this);
  ensures {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
{
  var k, tv: int;
  var {:layer 1} my_vis, my_vis1: SetInvoc;
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);

  k := 0;
  my_vis := Set_empty;

  while (k < tabLen)
    invariant {:layer 1} 0 <= k && k <= tabLen;
    invariant {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);
    invariant {:layer 1} (forall i: int :: 0 <= i && i < k
      ==> Map.ofSeq(Seq_restr(lin, my_vis))[i] != v);
    invariant {:layer 1} Set_subset(my_vis, Set_ofSeq(lin));
    invariant {:layer 1} (forall n1 : Invoc :: Set_elem(n1, my_vis)
      ==> Set_elem(n1, tabvis[invoc_k(n1)]));
    invariant {:layer 1} (forall n1 : Invoc :: Set_elem(n1, my_vis)
      ==> 0 <= invoc_k(n1) && invoc_k(n1) < k);
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
      call intro_writeVis(this, my_vis);
      call intro_add_tabvis(tabLen-1, this);
      call intro_writeLin(this);
      witness_k := k;

      res := true;

      yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
        && postLP(called, returned, lin, this);
      assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
        Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
      return;
    }
    k := k + 1;
    yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this)
      && (forall i: int :: 0 <= i && i < k ==> Map.ofSeq(Seq_restr(lin, my_vis))[i] != v)
      && Set_subset(my_vis, Set_ofSeq(lin))
      && (forall n1 : Invoc :: Set_elem(n1, my_vis) ==> Set_elem(n1, tabvis[invoc_k(n1)]))
      && (forall n1 : Invoc :: Set_elem(n1, my_vis) ==> 0 <= invoc_k(n1) && invoc_k(n1) < k);
      assert {:layer 1} (forall n1, n2: Invoc :: hb(n1, this) && Set_elem(n2, vis[n1])
         && 0 <= invoc_k(n2) && invoc_k(n2) < k ==> Set_elem(n2, my_vis));
  }
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this)
    && (forall i: int :: 0 <= i && i < tabLen ==> Map.ofSeq(Seq_restr(lin, my_vis))[i] != v)
    && (forall n1 : Invoc :: Set_elem(n1, my_vis) ==> Set_elem(n1, tabvis[invoc_k(n1)]))
    && (forall n1 : Invoc :: Set_elem(n1, my_vis) ==> 0 <= invoc_k(n1) && invoc_k(n1) < tabLen)
    && (forall n1, n2: Invoc :: hb(n1, this) && Set_elem(n2, vis[n1])
                         && 0 <= invoc_k(n2) && invoc_k(n2) < k
                         ==> Set_elem(n2, my_vis));

  // Linearization point
  call intro_writeVis(this, my_vis);
  call intro_add_tabvis(tabLen-1, this);
  call intro_writeLin(this);
  witness_k := k;

  res := false;

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
    && postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
}