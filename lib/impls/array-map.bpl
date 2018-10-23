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

// ---------- The ADT methods

procedure {:atomic} {:layer 2} put_spec(args: ArgList)
  modifies abs, lin, vis;
{
  var {:linear "this"} this: Invoc;
  var my_vis: SetInvoc;

  var k: int;
  var v: int;

  assume put == Invoc.name(this);
  assume args == Invoc.args(this);

  k := args[0];
  v := args[1];

  lin := Seq_append(lin, this);
  vis[this] := my_vis;
  // Put is complete
  assume my_vis == Set_ofSeq(lin);

  // Put satisfies its functional spec
  abs[k] := v;
}

procedure {:yields} {:layer 1} {:refines "put_spec"} put(args: ArgList)
  requires {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  requires {:layer 1} 0 <= args[0] && args[0] < tabLen;
  ensures {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
{
  var {:linear "this"} this: Invoc;
  var {:layer 1} my_vis: SetInvoc;

  var k: int;
  var v: int;

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  call this := spec_call(put, args);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && pending(called, returned, this);

  k := args[0];
  v := args[1];

  call writeTable(k, v);

  call intro_add_tabvis(k, this);
  call my_vis := intro_read_tabvis_range(0, tabLen);
  call intro_write_vis(this, my_vis);
  call intro_writeAbs(k, v);
  call intro_writeLin(this);

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
    && pending(called, returned, this) && Seq_elem(this, lin);
  call spec_return(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
}


procedure {:atomic} {:layer 2} get_spec(args: ArgList) returns (v: int)
  modifies lin, vis;
{
  var {:linear "this"} this: Invoc; var my_vis: SetInvoc;

  var k: int;

  assume get == Invoc.name(this);
  assume args == Invoc.args(this);

  k := args[0];

  lin := Seq_append(lin, this);
  vis[this] := my_vis;
  // Get is complete -- TODO make predicate
  assume my_vis == Set_ofSeq(lin);

  // Get satisfies its functional spec
  v := abs[k];
}

procedure {:yields} {:layer 1} {:refines "get_spec"} get(args: ArgList)
  returns (v: int)
  requires {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  requires {:layer 1} 0 <= args[0] && args[0] < tabLen;
  ensures {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
{
  var {:linear "this"} this: Invoc;
  var {:layer 1} my_vis: SetInvoc;

  var k: int;

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  call this := spec_call(get, args);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && pending(called, returned, this);

  k := args[0];

  call v := readTable(k);

  call intro_add_tabvis(k, this);
  call my_vis := intro_read_tabvis_range(0, tabLen);
  call intro_write_vis(this, my_vis);
  call intro_writeLin(this);

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
    && pending(called, returned, this) && Seq_elem(this, lin);
  call spec_return(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
}


function contains_func_spec(vis: SetInvoc, lin: SeqInvoc, witness_k: int,
                            v: int, res: bool) : bool
{
   (res ==> state(vis, lin)[witness_k] == v)
   && (!res ==> (forall i: int :: 0 <= i && i < tabLen ==> state(vis, lin)[i] != v))
}

procedure {:atomic} {:layer 2} contains_spec(args: ArgList)
  returns (res: bool, witness_k: int)
  modifies lin, vis;
{
  var {:linear "this"} this: Invoc;
  var my_vis: SetInvoc;

  var v: int;

  assume contains == Invoc.name(this);
  assume args == Invoc.args(this);
  assume tabLen - 1 == invoc_k(this);

  v := args[0];

  lin := Seq_append(lin, this);
  vis[this] := my_vis;
  // Contains is monotonic
  assume (forall j: Invoc :: hb(j, this) ==> Set_subset(vis[j], my_vis));

  // Contains satisfies its functional spec
  assume contains_func_spec(my_vis, lin, witness_k, v, res);
}

procedure {:yields} {:layer 1} {:refines "contains_spec"} contains(args: ArgList)
  returns (res: bool, witness_k: int)
  requires {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  ensures {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
{
  var k, tv: int;
  var {:linear "this"} this: Invoc;
  var {:layer 1} my_vis, my_vis1: SetInvoc;

  var v: int;

  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  call this := spec_call(contains, args);
  assume tabLen - 1 == invoc_k(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && pending(called, returned, this);

  v := args[0];

  k := 0;
  my_vis := Set_empty;

  while (k < tabLen)
    invariant {:layer 1} 0 <= k && k <= tabLen;
    invariant {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && pending(called, returned, this);
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
    call lemma_state_Set_union(k, tabLen, my_vis, my_vis1);
    my_vis := Set_union(my_vis, my_vis1);

    if (tv == v) {
      // Linearization point
      call my_vis1 := intro_read_tabvis_range(k+1, tabLen);
      assert {:layer 1} (forall n1, n2: Invoc ::
                          hb(n1, this) && Set_elem(n2, vis[n1])
                          && 0 <= invoc_k(n2) && invoc_k(n2) < k+1
                          ==> Set_elem(n2, my_vis));
      call lemma_state_Set_union(k+1, tabLen, my_vis, my_vis1);
      my_vis := Set_union(my_vis, my_vis1);
      call intro_write_vis(this, my_vis);
      call intro_add_tabvis(tabLen-1, this);
      call intro_writeLin(this);
      witness_k := k;

      res := true;

      yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned)
        && pending(called, returned, this) && Seq_elem(this, lin);
      call spec_return(this);
      yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
      return;
    }
    k := k + 1;
    yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && pending(called, returned, this)
      && (forall i: int :: 0 <= i && i < k ==> state(my_vis, lin)[i] != v)
      && Set_subset(my_vis, Set_ofSeq(lin))
      && (forall n1 : Invoc :: Set_elem(n1, my_vis) ==> Set_elem(n1, tabvis[invoc_k(n1)]))
      && (forall n1 : Invoc :: Set_elem(n1, my_vis) ==> 0 <= invoc_k(n1) && invoc_k(n1) < k);
      assert {:layer 1} (forall n1, n2: Invoc :: hb(n1, this) && Set_elem(n2, vis[n1])
         && 0 <= invoc_k(n2) && invoc_k(n2) < k ==> Set_elem(n2, my_vis));
  }
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned) && pending(called, returned, this)
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
    && pending(called, returned, this) && Seq_elem(this, lin);
  call spec_return(this);
  yield; assert {:layer 1} tableInv(table, abs, tabvis, lin, vis, tabLen, called, returned);
  return;
}
