// ----------------------------------------
// A simplified hash table implementation with weakly consistent contains method.
//
// Compared to Java's hash map, we assume:
// - The hash function is identity
// - Each bucket stores a single value as opposed to a list
// - There is no resizing of the hash table
//
// Use options -noinfer -typeEncoding:m -useArrayTheory
// ----------------------------------------


// ---------- Shared state and invariant

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

  // tabvis[i] contains everything in lin of key i
  && (forall i: int :: 0 <= i && i < tabLen
    ==> Set_subset(Map.restr(Set_ofSeq(lin), i), tabvis[i]))
  // lin|tabvis[i] gives value of key i
  && (forall i: int :: 0 <= i && i < tabLen
    ==> Map.ofSeq(Seq_restr(lin, tabvis[i]))[i] == abs[i])
  // tabvis only contains linearized things
  && (forall i: int :: 0 <= i && i < tabLen
    ==> Set_subset(tabvis[i], Set_ofSeq(lin)))
  // tabvis[i] only has puts to key k
  && (forall i: int, n: Invoc :: 0 <= i && i < tabLen && Set_elem(n, tabvis[i])
    ==> invoc_m(n) == Map.put && invoc_k(n) == i)

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


procedure {:yields} {:layer 1} {:refines "get_call_atomic"}
    get_call({:linear "this"} this: Invoc)
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

  call my_vis := intro_readLin();
  call intro_writeVis(this, my_vis);
  call intro_writeLin(this);

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
    && postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
}

procedure {:yields} {:layer 1} {:refines "get_return_atomic"}
    get_return({:linear "this"} this: Invoc)
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


procedure {:yields} {:layer 1} {:refines "contains_call_atomic"}
    contains_call({:linear "this"} this: Invoc)
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
  yield;
  assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);

  k := 0;
  call my_vis := intro_readLin();
  yield;
  assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);
  assert {:layer 1} (forall j: Invoc :: hb(j, this) ==> Set_subset(vis[j], my_vis));
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, my_vis)}
    Set_elem(n1, my_vis) ==> Set_elem(n1, Set_ofSeq(lin)));
  assert {:layer 1} (forall i: int :: 0 <= i && i < tabLen
    ==> Set_subset(Map.restr(my_vis, i), tabvis[i]));

  while (k < tabLen)
    invariant {:layer 1} 0 <= k && k <= tabLen;
    invariant {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);
    invariant {:layer 1} (forall i: int :: 0 <= i && i < k
      ==> Map.ofSeq(Seq_restr(lin, my_vis))[i] != v);
    invariant {:layer 1} (forall j: Invoc :: hb(j, this) ==> Set_subset(vis[j], my_vis));
    invariant {:layer 1} (forall n1: Invoc :: {Set_elem(n1, my_vis)}
      Set_elem(n1, my_vis) ==> Set_elem(n1, Set_ofSeq(lin)));
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

      yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
        && postLP(called, returned, lin, this);
      assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
        Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
      return;
    }
    k := k + 1;
    yield;
    assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);
    assert {:layer 1} (forall i: int :: 0 <= i && i < k
      ==> Map.ofSeq(Seq_restr(lin, my_vis))[i] != v);
    assert {:layer 1} (forall j: Invoc :: hb(j, this) ==> Set_subset(vis[j], my_vis));
    assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, my_vis)}
      Set_elem(n1, my_vis) ==> Set_elem(n1, Set_ofSeq(lin)));
    assert {:layer 1} (forall i: int :: 0 <= i && i < tabLen
      ==> Set_subset(Map.restr(my_vis, i), tabvis[i]));
  }
  yield;
  assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && preLP(called, returned, lin, this);
  assert {:layer 1} (forall i: int :: 0 <= i && i < tabLen
    ==> Map.ofSeq(Seq_restr(lin, my_vis))[i] != v);
  assert {:layer 1} (forall j: Invoc :: hb(j, this) ==> Set_subset(vis[j], my_vis));
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, my_vis)}
    Set_elem(n1, my_vis) ==> Set_elem(n1, Set_ofSeq(lin)));

  // Linearization point
  call intro_writeVis(this, my_vis);
  call intro_writeLin(this);
  witness_k := k;

  res := false;

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
    && postLP(called, returned, lin, this);
  assert {:layer 1} (forall n1: Invoc :: {Set_elem(n1, vis[this])}
    Set_elem(n1, vis[this]) ==> Set_elem(n1, Set_ofSeq(lin)));
}

procedure {:yields} {:layer 1} {:refines "contains_return_atomic"}
    contains_return({:linear "this"} this: Invoc)
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
