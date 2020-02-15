// ----------------------------------------
// A simplified hash table implementation with weakly consistent contains method
// The hash function is assumed to be injective for simplicity,
// otherwise one needs to have lists at each bucket to deal with hash collisions
// ----------------------------------------


/** Sets and Sequences */

// ---------- Types and axiomatization of sets (of invocations)

type SetInvoc = [Invoc]bool;

function Set_card(SetInvoc): int;
axiom (forall s: SetInvoc :: { Set_card(s) } 0 <= Set_card(s));

function Set_empty(): SetInvoc;
axiom (forall o: Invoc :: { Set_empty()[o] } !Set_empty()[o]);
axiom (forall s: SetInvoc :: { Set_card(s) }
  (Set_card(s) == 0 <==> s == Set_empty()) &&
  (Set_card(s) != 0 ==> (exists x: Invoc :: s[x])));

// the empty set could be of anything
//axiom (forall t: Ty :: { $Is(Set_empty() : [Invoc]bool, TSet(t)) } $Is(Set_empty() : [Invoc]bool, TSet(t)));

function Set(Invoc): SetInvoc;
axiom (forall r: Invoc :: { Set(r) } Set(r)[r]);
axiom (forall r: Invoc, o: Invoc :: { Set(r)[o] } Set(r)[o] <==> r == o);
axiom (forall r: Invoc :: { Set_card(Set(r)) } Set_card(Set(r)) == 1);

function Set_add(SetInvoc, Invoc): SetInvoc;
axiom (forall a: SetInvoc, x: Invoc, o: Invoc :: { Set_add(a,x)[o] }
  Set_add(a,x)[o] <==> o == x || a[o]);
axiom (forall a: SetInvoc, x: Invoc :: { Set_add(a, x) }
  Set_add(a, x)[x]);
axiom (forall a: SetInvoc, x: Invoc, y: Invoc :: { Set_add(a, x), a[y] }
  a[y] ==> Set_add(a, x)[y]);
axiom (forall a: SetInvoc, x: Invoc :: { Set_card(Set_add(a, x)) }
  a[x] ==> Set_card(Set_add(a, x)) == Set_card(a));
axiom (forall a: SetInvoc, x: Invoc :: { Set_card(Set_add(a, x)) }
  !a[x] ==> Set_card(Set_add(a, x)) == Set_card(a) + 1);

function Set_union(SetInvoc, SetInvoc): SetInvoc;
axiom (forall a: SetInvoc, b: SetInvoc, o: Invoc :: { Set_union(a,b)[o] }
  Set_union(a,b)[o] <==> a[o] || b[o]);
axiom (forall a, b: SetInvoc, y: Invoc :: { Set_union(a, b), a[y] }
  a[y] ==> Set_union(a, b)[y]);
axiom (forall a, b: SetInvoc, y: Invoc :: { Set_union(a, b), b[y] }
  b[y] ==> Set_union(a, b)[y]);
axiom (forall a, b: SetInvoc :: { Set_union(a, b) }
  Set_disjoint(a, b) ==>
    Set_diff(Set_union(a, b), a) == b &&
    Set_diff(Set_union(a, b), b) == a);
// Follows from the general union axiom, but might be still worth including, because disjoint union is a common case:
// axiom (forall a, b: SetInvoc :: { Set_card(Set_union(a, b)) }
//   Set_disjoint(a, b) ==>
//     Set_card(Set_union(a, b)) == Set_card(a) + Set_card(b));

function Set_inter(SetInvoc, SetInvoc): SetInvoc;
axiom (forall a: SetInvoc, b: SetInvoc, o: Invoc :: { Set_inter(a,b)[o] }
  Set_inter(a,b)[o] <==> a[o] && b[o]);

axiom (forall a, b: SetInvoc :: { Set_union(Set_union(a, b), b) }
  Set_union(Set_union(a, b), b) == Set_union(a, b));
axiom (forall a, b: SetInvoc :: { Set_union(a, Set_union(a, b)) }
  Set_union(a, Set_union(a, b)) == Set_union(a, b));
axiom (forall a, b: SetInvoc :: { Set_inter(Set_inter(a, b), b) }
  Set_inter(Set_inter(a, b), b) == Set_inter(a, b));
axiom (forall a, b: SetInvoc :: { Set_inter(a, Set_inter(a, b)) }
  Set_inter(a, Set_inter(a, b)) == Set_inter(a, b));
axiom (forall a, b: SetInvoc :: { Set_card(Set_union(a, b)) }{ Set_card(Set_inter(a, b)) }
  Set_card(Set_union(a, b)) + Set_card(Set_inter(a, b)) == Set_card(a) + Set_card(b));

function Set_diff(SetInvoc, SetInvoc): SetInvoc;
axiom (forall a: SetInvoc, b: SetInvoc, o: Invoc :: { Set_diff(a,b)[o] }
  Set_diff(a,b)[o] <==> a[o] && !b[o]);
axiom (forall a, b: SetInvoc, y: Invoc :: { Set_diff(a, b), b[y] }
  b[y] ==> !Set_diff(a, b)[y] );
axiom (forall a, b: SetInvoc ::
  { Set_card(Set_diff(a, b)) }
  Set_card(Set_diff(a, b)) + Set_card(Set_diff(b, a))
  + Set_card(Set_inter(a, b))
    == Set_card(Set_union(a, b)) &&
  Set_card(Set_diff(a, b)) == Set_card(a) - Set_card(Set_inter(a, b)));

function Set_subset(SetInvoc, SetInvoc): bool;
axiom(forall a: SetInvoc, b: SetInvoc :: { Set_subset(a,b) }
  Set_subset(a,b) <==> (forall o: Invoc :: {a[o]} {b[o]} a[o] ==> b[o]));
// axiom(forall a: SetInvoc, b: SetInvoc ::
//   { Set_subset(a,b), Set_card(a), Set_card(b) }  // very restrictive trigger
//   Set_subset(a,b) ==> Set_card(a) <= Set_card(b));


function Set_equal(SetInvoc, SetInvoc): bool;
axiom(forall a: SetInvoc, b: SetInvoc :: { Set_equal(a,b) }
  Set_equal(a,b) <==> (forall o: Invoc :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom(forall a: SetInvoc, b: SetInvoc :: { Set_equal(a,b) }  // extensionality axiom for sets
  Set_equal(a,b) ==> a == b);

function Set_disjoint(SetInvoc, SetInvoc): bool;
axiom (forall a: SetInvoc, b: SetInvoc :: { Set_disjoint(a,b) }
  Set_disjoint(a,b) <==> (forall o: Invoc :: {a[o]} {b[o]} !a[o] || !b[o]));


// ---------- Types and axiomatization of sequences (of invocations)

// Sequences of invocations
type SeqInvoc;

function Seq_append(s: SeqInvoc, o: Invoc) returns (t: SeqInvoc);

function Seq_elem(n: Invoc, s: SeqInvoc) : bool;

// Relationship between elem and append
axiom (forall n1, n2: Invoc, s: SeqInvoc :: {Seq_elem(n1, Seq_append(s, n2))}
       Seq_elem(n1, Seq_append(s, n2)) <==> Seq_elem(n1, s) || n1 == n2);


// -- New functions and axioms:

function Set_ofSeq(q: SeqInvoc) returns (s: SetInvoc);

// Relation between Set_ofSeq, add, and append
axiom (forall q: SeqInvoc, n: Invoc :: {Set_ofSeq(Seq_append(q, n))}
  Set_ofSeq(Seq_append(q, n)) == Set_add(Set_ofSeq(q), n));

// Relation between Set_ofSeq, Set_elem, and Seq_elem
axiom (forall q: SeqInvoc, n: Invoc :: {Set_ofSeq(q)[n]}
  Seq_elem(n, q) <==> Set_ofSeq(q)[n]);

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
  Seq_distinct(Seq_append(q, n)) && !s[n]
  ==> Seq_restr(Seq_append(q, n), Set_add(s, n)) == Seq_append(Seq_restr(q, s), n));

// Relation between Seq_elem and Seq_restr
axiom (forall q: SeqInvoc, s: SetInvoc, n: Invoc :: {Seq_elem(n, Seq_restr(q, s))}
  Seq_elem(n, Seq_restr(q, s)) <==> Seq_elem(n, q) && s[n]);


// Implicit (strict) order of a sequence
function Seq_ord(q: SeqInvoc, n1, n2: Invoc) : bool;

// This order is transitive
// axiom (forall q: SeqInvoc, n1, n2, n3: Invoc :: //{}
//   Seq_ord(q, n1, n2) && Seq_ord(q, n2, n3) ==> Seq_ord(q, n1, n3));

// Adding to the restriction set is append if ordered correctly
axiom (forall q: SeqInvoc, s: SetInvoc, n: Invoc ::
    {Seq_append(Seq_restr(q, s), n)}
  (forall n1: Invoc :: Seq_elem(n1, Seq_restr(q, s)) ==> Seq_ord(q, n1, n))
  && Seq_elem(n, q) && !s[n]
  ==> Seq_restr(q, Set_add(s, n)) == Seq_append(Seq_restr(q, s), n));

// Appending extends order
axiom (forall q: SeqInvoc, n, n1, n2: Invoc :: {Seq_ord(Seq_append(q, n), n1, n2)}
  Seq_distinct(q) ==>
  (Seq_ord(Seq_append(q, n), n1, n2)
    <==> (Seq_elem(n1, q) && Seq_elem(n2, q) && Seq_ord(q, n1, n2))
      || (Seq_elem(n1, q) && n2 == n)));


/** Executions and Invocations */

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

// hb[x][y] : x happens-before y.
var {:layer 1,2} hb: [Invoc][Invoc]bool;

// A shared global variable that builds the linearization
var {:layer 1,2} lin: SeqInvoc;

// A map from invocations to the set of prior invocations visible to them
var {:layer 1,2} vis: [Invoc]SetInvoc;

// The map from invocations to method and argument values is encoded in the Invoc
// type so as to not further complicate the ADT axioms.

// The map from invocations to return values
// Since return values are determined at the LPs, we store them at LP time.
type RetVal;
function RetVal_ofInt(int) : RetVal;
function RetVal_ofBool(bool) : RetVal;
var {:layer 1,2} ret: [Invoc]RetVal;

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
  requires {:layer 1} (forall n1 : Invoc :: hb[n1][n] ==> Seq_elem(n1, lin));
  ensures {:layer 1} Seq_elem(n, lin);
  modifies lin;
{
  lin := Seq_append(lin, n);
}

procedure {:layer 1} {:inline 1} intro_writeHb(n1: Invoc, n2: Invoc)
  modifies hb;
{
  hb[n1] := hb[n1][n2 := true];
}

procedure {:layer 1} {:inline 1} intro_writeRet(n: Invoc, v: RetVal)
  modifies ret;
{
  ret[n] := v;
}


// ---------- Consistency levels

function {:inline} Consistency.absolute(hb: [Invoc]SetInvoc, lin: SeqInvoc,
    vis: [Invoc]SetInvoc, n: Invoc, n_vis: SetInvoc): bool {
  n_vis == Set_ofSeq(lin)
}

function {:inline} Consistency.monotonic(hb: [Invoc]SetInvoc, lin: SeqInvoc,
    vis: [Invoc]SetInvoc, n: Invoc, n_vis: SetInvoc): bool {
  (forall i: Invoc :: hb[i][n] ==> Set_subset(vis[i], n_vis))
}


/** Map ADT */

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
  invoc_m(n) == Map.put ==>
        Map.restr(Set_ofSeq(Seq_append(q, n)), invoc_k(n))
          == Set_add(Map.restr(Set_ofSeq(q), invoc_k(n)), n));

// Adding invocations not on k preserves Map.restr
axiom (forall q: SeqInvoc, n: Invoc, k: int ::
  invoc_k(n) != k || invoc_m(n) != Map.put
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

// Map.restr to k doesn't change if we take union with stuff != k
axiom (forall s, t: SetInvoc, k: int :: {Map.restr(Set_union(s, t), k)}
  (forall n: Invoc :: t[n] ==> invoc_m(n) != Map.put || invoc_k(n) != k)
  ==> Map.restr(Set_union(s, t), k) == Map.restr(s, k));

// Union of disjoint keys means state comes from one of the two sets
procedure {:layer 1} lemma_state_Set_union(k: int, s, t: SetInvoc);
  requires (forall n: Invoc :: s[n] ==> invoc_k(n) < k);
  requires (forall n: Invoc :: t[n] ==> k <= invoc_k(n));
  ensures (forall i: int :: 0 <= i && i < k ==>
    Map.ofSeq(Seq_restr(lin, Set_union(s, t)))[i] == Map.ofSeq(Seq_restr(lin, s))[i]);
  ensures (forall i: int :: k <= i && i < tabLen ==>
    Map.ofSeq(Seq_restr(lin, Set_union(s, t)))[i] == Map.ofSeq(Seq_restr(lin, t))[i]);


// ---------- Atomic specification program:

procedure {:atomic} {:layer 2} hb_action_atomic(n1: Invoc, n2: Invoc)
  modifies hb;
{
  hb[n1] := hb[n1][n2 := true];
}

procedure {:atomic} {:layer 2} put_call_atomic({:linear "this"} this: Invoc) {}

procedure {:atomic} {:layer 2} put_atomic(k: int, v: int, {:linear "this"} this: Invoc)
  modifies lin, vis;
{
  var my_vis: SetInvoc;

  // Satisfies its functional spec
  assume true;

  assume Consistency.absolute(hb, lin, vis, this, my_vis);

  lin := Seq_append(lin, this);
  vis[this] := my_vis;
}

procedure {:atomic} {:layer 2} put_return_atomic({:linear "this"} this: Invoc) {}

procedure {:atomic} {:layer 2} get_call_atomic({:linear "this"} this: Invoc) {}

procedure {:atomic} {:layer 2} get_atomic(k: int, {:linear "this"} this: Invoc) returns (v: int)
  modifies lin, vis, ret;
{
  var my_vis: SetInvoc;

  // Get satisfies its functional spec
  assume v == Map.ofSeq(Seq_restr(lin, my_vis))[k];

  assume Consistency.absolute(hb, lin, vis, this, my_vis);

  lin := Seq_append(lin, this);
  vis[this] := my_vis;

  ret[this] := RetVal_ofInt(v);
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

procedure {:atomic} {:layer 2} contains_atomic(v: int, {:linear "this"} this: Invoc)
  returns (res: bool, witness_k: int)
  modifies lin, vis, ret;
{
  var my_vis: SetInvoc;

  // Contains satisfies its functional spec
  assume contains_func_spec(my_vis, lin, witness_k, v, res);

  assume Consistency.monotonic(hb, lin, vis, this, my_vis);

  lin := Seq_append(lin, this);
  vis[this] := my_vis;

  ret[this] := RetVal_ofBool(res);
}

procedure {:atomic} {:layer 2} contains_return_atomic({:linear "this"} this: Invoc) {}


/** Map Implementation */

// ---------- Map implementation: Shared state and invariant

// Concrete state of implementation
var {:layer 0,1} table: [int]int;
const tabLen: int;
axiom 0 < tabLen;

// The hash function
function hash(k: int) : int;
axiom (forall k: int :: 0 <= hash(k) && hash(k) < tabLen);
// Assume the hash function is injective, for simplicity
axiom (forall k1, k2: int :: hash(k1) == hash(k2) ==> k1 == k2);

// Visibility per location of concrete state
var {:layer 1,1} tabvis: [int]SetInvoc;


// The set of invocations that have been called
var {:layer 1,1} called: [Invoc]bool;

// The set of invocations that have returned
var {:layer 1,1} returned: [Invoc]bool;

// The invariants
function {:inline} tableInv(table: [int]int, tabvis: [int]SetInvoc,
                            hb: [Invoc][Invoc]bool, lin: SeqInvoc, vis: [Invoc]SetInvoc, tabLen: int,
                            called: [Invoc]bool, returned: [Invoc]bool) : bool
{
  // tabvis only contains linearized things
  (forall i: int :: 0 <= i && i < tabLen
    ==> Set_subset(tabvis[i], Set_ofSeq(lin)))
  // tabvis[i] contains everything in lin of keys that hash to i
  && (forall k: int :: 0 <= hash(k) && hash(k) < tabLen
    ==> Set_subset(Map.restr(Set_ofSeq(lin), k), tabvis[hash(k)]))
  // tabvis[i] only has puts to keys that hash to i
  && (forall i: int, n: Invoc :: 0 <= i && i < tabLen && tabvis[i][n]
    ==> invoc_m(n) == Map.put && hash(invoc_k(n)) == i)
  // lin|tabvis[i] gives value of keys that hash to i
  && (forall k: int ::
    Map.ofSeq(Seq_restr(lin, tabvis[hash(k)]))[k] == table[hash(k)])

  // ---- Invariants of the specification program:
  // lin only contains called things
  && (forall n: Invoc :: {Seq_elem(n, lin)} Seq_elem(n, lin) ==> called[n])
  // lin contains distinct elements
  && Seq_distinct(lin)
  // vis sets only contain linearized ops
  && (forall n1, n2: Invoc :: {vis[n2][n1]}
    vis[n2][n1] && returned[n2] ==> Set_ofSeq(lin)[n1])
  // Used to infer that invocations don't modify vis after they've returned
  && (forall n1, n2 : Invoc :: called[n1] && hb[n2][n1] ==> returned[n2])
  // To establish precondition of intro_writeLin
  && (forall n: Invoc :: returned[n] ==> Seq_elem(n, lin))
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

// Write to the table
procedure {:atomic} {:layer 1} writeTable_atomic(k, v: int)
  modifies table;
{
  table[k] := v;
}
procedure {:yields} {:layer 0} {:refines "writeTable_atomic"}
  writeTable(k, v: int);

// Read from the table
procedure {:atomic} {:layer 1} readTable_atomic(k: int)
  returns (v: int)
{
  v := table[k];
}
procedure {:yields} {:layer 0} {:refines "readTable_atomic"} readTable(k: int)
  returns (v: int);


// ---------- Primitives for manipulating logical/abstract state

procedure {:layer 1} intro_add_tabvis(i: int, n: Invoc)
  ensures {:layer 1} tabvis == old(tabvis)[i := Set_add(old(tabvis)[i], n)];
  modifies tabvis;
{
  tabvis[i] := Set_add(tabvis[i], n);
}

procedure {:layer 1} intro_read_tabvis(i: int) returns (s: SetInvoc)
  ensures {:layer 1} s == tabvis[i];
{
  s := tabvis[i];
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


procedure {:yields} {:layer 1} {:refines "hb_action_atomic"}
    hb_action(n1: Invoc, n2: Invoc)
  requires {:layer 1} returned[n1] && !called[n2];
{
  call intro_writeHb(n1, n2);
  yield;
}


procedure {:yields} {:layer 1} {:refines "put_call_atomic"}
    put_call({:linear "this"} this: Invoc)
  requires {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  // everything before this has returned
  requires {:layer 1} (forall n1: Invoc :: hb[n1][this] ==> returned[n1]);
  // this has not been called or returned yet
  requires {:layer 1} (!called[this] && !returned[this]);
  ensures {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  ensures {:layer 1} preLP(called, returned, lin, this);
  modifies called;
{
  call intro_writeCalled(this);

  yield;
  assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  assert {:layer 1} preLP(called, returned, lin, this);
}

procedure {:yields} {:layer 1} {:refines "put_atomic"} put(k, v: int, {:linear "this"} this: Invoc)
  requires {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  requires {:layer 1} preLP(called, returned, lin, this);
  requires {:layer 1} invoc_m(this) == Map.put && invoc_k(this) == k && invoc_v(this) == v;
  requires {:layer 1} 0 <= k && k < tabLen;
  ensures {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  ensures {:layer 1} postLP(called, returned, lin, this);
  ensures {:layer 1} (forall n1: Invoc :: {vis[this][n1]}
    vis[this][n1] ==> Set_ofSeq(lin)[n1]);
{
  var {:layer 1} my_vis: SetInvoc;
  yield; assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);

  call writeTable(hash(k), v);

  call intro_add_tabvis(hash(k), this);
  call my_vis := intro_readLin();
  call intro_writeLin(this);
  call intro_writeVis(this, my_vis);

  yield; assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned)
    && postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {vis[this][n1]}
    vis[this][n1] ==> Set_ofSeq(lin)[n1]);
}

procedure {:yields} {:layer 1} {:refines "put_return_atomic"}
    put_return({:linear "this"} this: Invoc)
  requires {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  requires {:layer 1} postLP(called, returned, lin, this);
  requires {:layer 1} (forall n1: Invoc :: {vis[this][n1]}
    vis[this][n1] ==> Set_ofSeq(lin)[n1]);
  ensures {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  modifies returned;
{
  call intro_writeReturned(this);

  yield;
  assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
}


procedure {:yields} {:layer 1} {:refines "get_call_atomic"}
    get_call({:linear "this"} this: Invoc)
  requires {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  // everything before this has returned
  requires {:layer 1} (forall n1: Invoc :: hb[n1][this] ==> returned[n1]);
  // this has not been called or returned yet
  requires {:layer 1} (!called[this] && !returned[this]);
  ensures {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  ensures {:layer 1} preLP(called, returned, lin, this);
  modifies called;
{
  call intro_writeCalled(this);

  yield;
  assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  assert {:layer 1} preLP(called, returned, lin, this);
}

procedure {:yields} {:layer 1} {:refines "get_atomic"} get(k: int, {:linear "this"} this: Invoc)
  returns (v: int)
  requires {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  requires {:layer 1} preLP(called, returned, lin, this);
  requires {:layer 1} invoc_m(this) == Map.get && invoc_k(this) == k;
  requires {:layer 1} 0 <= k && k < tabLen;
  ensures {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  ensures {:layer 1} postLP(called, returned, lin, this);
  ensures {:layer 1} (forall n1: Invoc :: {vis[this][n1]}
    vis[this][n1] ==> Set_ofSeq(lin)[n1]);
{
  var {:layer 1} my_vis: SetInvoc;
  yield; assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);

  call v := readTable(hash(k));

  call my_vis := intro_readLin();
  call intro_writeVis(this, my_vis);
  call intro_writeLin(this);
  call intro_writeRet(this, RetVal_ofInt(v));

  yield; assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned)
    && postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {vis[this][n1]}
    vis[this][n1] ==> Set_ofSeq(lin)[n1]);
}

procedure {:yields} {:layer 1} {:refines "get_return_atomic"}
    get_return({:linear "this"} this: Invoc)
  requires {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  requires {:layer 1} postLP(called, returned, lin, this);
  requires {:layer 1} (forall n1: Invoc :: {vis[this][n1]}
    vis[this][n1] ==> Set_ofSeq(lin)[n1]);
  ensures {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  modifies returned;
{
  call intro_writeReturned(this);

  yield;
  assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
}

procedure {:yields} {:layer 1} {:refines "contains_call_atomic"}
    contains_call({:linear "this"} this: Invoc)
  requires {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  // everything before this has returned
  requires {:layer 1} (forall n1: Invoc :: hb[n1][this] ==> returned[n1]);
  // this has not been called or returned yet
  requires {:layer 1} (!called[this] && !returned[this]);
  ensures {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  ensures {:layer 1} preLP(called, returned, lin, this);
  modifies called;
{
  call intro_writeCalled(this);

  yield;
  assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  assert {:layer 1} preLP(called, returned, lin, this);
}

procedure {:yields} {:layer 1} {:refines "contains_atomic"}
    contains(v: int, {:linear "this"} this: Invoc)
  returns (res: bool, witness_k: int)
  requires {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  requires {:layer 1} preLP(called, returned, lin, this);
  requires {:layer 1} invoc_m(this) == Map.contains && invoc_v(this) == v;
  ensures {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  ensures {:layer 1} postLP(called, returned, lin, this);
  ensures {:layer 1} (forall n1: Invoc :: {vis[this][n1]}
    vis[this][n1] ==> Set_ofSeq(lin)[n1]);
{
  var k, tv: int;
  var {:layer 1} my_vis, my_vis1: SetInvoc;
  yield;
  assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);

  k := 0;
  call my_vis := intro_readLin();
  yield;
  assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);
  assert {:layer 1} (forall j: Invoc :: hb[j][this] ==> Set_subset(vis[j], my_vis));
  assert {:layer 1} (forall n1: Invoc :: {my_vis[n1]}
    my_vis[n1] ==> Set_ofSeq(lin)[n1]);
  assert {:layer 1} (forall k1: int ::
    Set_subset(Map.restr(my_vis, k1), tabvis[hash(k1)]));

  while (k < tabLen)
    invariant {:layer 1} 0 <= k && k <= tabLen;
    invariant {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);
    invariant {:layer 1} (forall i: int :: 0 <= i && i < k
      ==> Map.ofSeq(Seq_restr(lin, my_vis))[i] != v);
    invariant {:layer 1} (forall j: Invoc :: hb[j][this] ==> Set_subset(vis[j], my_vis));
    invariant {:layer 1} (forall n1: Invoc :: {my_vis[n1]}
      my_vis[n1] ==> Set_ofSeq(lin)[n1]);
    invariant {:layer 1} (forall i: int :: 0 <= i && i < tabLen
      ==> Set_subset(Map.restr(my_vis, i), tabvis[i]));
  {
    // Read table[k] and add tabvis[k] to my_vis
    call tv := readTable(k);

    call my_vis1 := intro_read_tabvis(k);
    my_vis := Set_union(my_vis, my_vis1);

    assert {:layer 1} Map.restr(my_vis, k) == Map.restr(tabvis[k], k);
    assert {:layer 1} Map.ofSeq(Seq_restr(lin, tabvis[k]))[k]
      == Map.ofSeq(Seq_restr(lin, Map.restr(tabvis[k], k)))[k];

    assert {:layer 1} (forall i: int :: 0 <= i && i < k
      ==> Map.ofSeq(Seq_restr(lin, my_vis))[i] == Map.ofSeq(Seq_restr(lin, Map.restr(my_vis, i)))[i]);

    if (tv == v) {
      // Linearization point
      call intro_writeVis(this, my_vis);
      call intro_writeLin(this);
      witness_k := k;

      res := true;

      call intro_writeRet(this, RetVal_ofBool(res));
      yield; assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned)
        && postLP(called, returned, lin, this);
      assert {:layer 1} (forall n1: Invoc :: {vis[this][n1]}
        vis[this][n1] ==> Set_ofSeq(lin)[n1]);
      return;
    }
    k := k + 1;
    yield;
    assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} (forall i: int :: 0 <= i && i < k
      ==> Map.ofSeq(Seq_restr(lin, my_vis))[i] != v);
    assert {:layer 1} (forall j: Invoc :: hb[j][this] ==> Set_subset(vis[j], my_vis));
    assert {:layer 1} (forall n1: Invoc :: {my_vis[n1]}
      my_vis[n1] ==> Set_ofSeq(lin)[n1]);
    assert {:layer 1} (forall i: int :: 0 <= i && i < tabLen
      ==> Set_subset(Map.restr(my_vis, i), tabvis[i]));
  }
  yield;
  assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);
  assert {:layer 1} (forall i: int :: 0 <= i && i < tabLen
    ==> Map.ofSeq(Seq_restr(lin, my_vis))[i] != v);
  assert {:layer 1} (forall j: Invoc :: hb[j][this] ==> Set_subset(vis[j], my_vis));
  assert {:layer 1} (forall n1: Invoc :: {my_vis[n1]}
    my_vis[n1] ==> Set_ofSeq(lin)[n1]);

  // Linearization point
  call intro_writeVis(this, my_vis);
  call intro_writeLin(this);
  witness_k := k;

  res := false;

  call intro_writeRet(this, RetVal_ofBool(res));

  yield; assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned)
    && postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {vis[this][n1]}
    vis[this][n1] ==> Set_ofSeq(lin)[n1]);
}

procedure {:yields} {:layer 1} {:refines "contains_return_atomic"}
    contains_return({:linear "this"} this: Invoc)
  requires {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  requires {:layer 1} postLP(called, returned, lin, this);
  requires {:layer 1} (forall n1: Invoc :: {vis[this][n1]}
    vis[this][n1] ==> Set_ofSeq(lin)[n1]);
  ensures {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
  modifies returned;
{
  call intro_writeReturned(this);

  yield;
  assert {:layer 1} tableInv(table, tabvis, hb, lin, vis, tabLen, called, returned);
}