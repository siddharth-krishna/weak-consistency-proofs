// ---------- Logical and concrete shared state

// Abstract state of ADT
var {:layer 1,2} abs: Map.State;

// Visibility per location of concrete state
var {:layer 1,1} tabvis: [int]Set;


// Concrete state of implementation
var {:layer 0,1} table: [int]int;
const tabLen: int;
axiom 0 < tabLen;


function {:inline} abstracts(conc: [int]int, abs: Map.State) : bool
{
  (forall i: int :: 0 <= i && i < tabLen ==> conc[i] == abs[i])
}

// The invariants
function {:inline} tableInv(table: [int]int, tabLen: int, tabvis: [int]Set,
                            abs: Map.State,
                            lin: Seq, vis: Vis,
                            h: History) : bool
{
  abstracts(table, abs)
  && Set.unionAll(tabvis, 0, tabLen) == Set.ofSeq(lin)
  && (forall i: int :: 0 <= i && i < tabLen ==> Map.ofVis(tabvis[i], lin)[i] == abs[i])
  && (forall i: int :: 0 <= i && i < tabLen ==>
      Map.ofVis(tabvis[i], lin)[i] == Map.ofVis(Map.restr(Set.ofSeq(lin), i), lin)[i])
  && (forall i: int :: 0 <= i && i < tabLen ==> Set.subset(Map.restr(Set.ofSeq(lin), i), tabvis[i]))
  && (forall i: int :: 0 <= i && i < tabLen ==> Set.subset(tabvis[i], Set.ofSeq(lin)))
  && (forall i: int, n: Invoc :: 0 <= i && i < tabLen && Set.elem(n, tabvis[i])
      ==> Map.key(n) == i)
  // Used to infer that invocations don't modify vis after they've returned
  && (forall n1, n2 : Invoc :: History.called(h,n1) && hb(n2, n1) ==> History.returned(h,n2))
  // Sanity conditions on vis sets
  && (forall n1, n2 : Invoc :: Set.elem(n2, vis[n1]) ==> Set.elem(n2, tabvis[Map.key(n2)]))
  && (forall n1, n2 : Invoc :: Set.elem(n2, vis[n1]) ==> 0 <= Map.key(n2) && Map.key(n2) < tabLen)
  // To establish precondition of intro_writeLin
  && (forall n: Invoc :: History.returned(h,n) ==> Seq.elem(n, lin))
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

procedure {:layer 1} intro_add_tabvis(k: int, {:linear "this"} n: Invoc)
  // TODO why don't these follow from the body?
  ensures {:layer 1} tabvis == old(tabvis)[k := Set.add(old(tabvis)[k], n)];
  modifies tabvis;
{
  tabvis[k] := Set.add(tabvis[k], n);
}

procedure {:layer 1} intro_read_tabvis_range(i, j: int) returns (s: Set);
  ensures {:layer 1} s == Set.unionAll(tabvis, i, j);
  ensures {:layer 1} (forall n: Invoc, k: int :: Set.elem(n, tabvis[k]) && i <= k && k < j ==> Set.elem(n, s));
  // TODO show these
  ensures {:layer 1} (forall n1: Invoc :: Set.elem(n1, s) ==> Set.elem(n1, tabvis[Map.key(n1)]));
  ensures {:layer 1} (forall n1: Invoc :: Set.elem(n1, s)
    ==> i <= Map.key(n1) && Map.key(n1) < j);

procedure {:layer 1} intro_read_tabvis(k: int) returns (s: Set)
  ensures {:layer 1} s == tabvis[k];
{
  s := tabvis[k];
}

procedure {:layer 1} intro_write_vis({:linear "this"} n: Invoc, s: Set)
  modifies vis;
  ensures {:layer 1} vis == old(vis)[n := s];
{
  vis[n] := s;
}

procedure {:layer 1} {:inline 1} intro_writeLin({:linear "this"} n: Invoc)
  // To show that linearization is consistent with happens-before
  requires {:layer 1} (forall n1 : Invoc :: hb(n1, n) ==> Seq.elem(n1, lin));
  modifies lin;
{
  lin := Seq.append(lin, n);
}

procedure {:layer 1} {:inline 1} intro_writeAbs(k: int, v: int)
  modifies abs;
{
  abs[k] := v;
}

/**
 * ADT method specifications
 */

procedure {:atomic} {:layer 2} put_spec(args: ArgList) returns (rets: ArgList)
  modifies abs, lin, vis;
{
  var {:linear "this"} this: Invoc;
  var my_vis: Set;

  assume Invoc.match(this, Map.put, args, rets);

  lin := Seq.append(lin, this);
  vis[this] := my_vis;
  assume Consistency.complete(lin, vis, this);

  // Put satisfies its functional spec
  // FIXME
  abs[args[0]] := args[1];
  // assume Map.spec.put(my_vis, lin, args);
}

procedure {:atomic} {:layer 2} get_spec(args: ArgList) returns (rets: ArgList)
  modifies lin, vis;
{
  var {:linear "this"} this: Invoc;
  var my_vis: Set;

  assume Invoc.match(this, Map.get, args, rets);

  lin := Seq.append(lin, this);
  vis[this] := my_vis;
  assume Consistency.complete(lin, vis, this);

  // Get satisfies its functional spec
  assume Map.spec.get(my_vis, lin, args, rets);
}

procedure {:atomic} {:layer 2} contains_spec(args: ArgList) returns (rets: ArgList)
  modifies lin, vis;
{
  var {:linear "this"} this: Invoc;
  var my_vis: Set;

  assume Invoc.match(this, Map.contains, args, rets);

  // FIXME this is a bit special...
  assume tabLen - 1 == Map.key(this);

  lin := Seq.append(lin, this);
  vis[this] := my_vis;
  assume Consistency.monotonic(lin, vis, this);

  // Contains satisfies its functional spec
  assume Map.spec.contains(my_vis, lin, tabLen, args, rets);
}

/**
 * ADT method implementations
 */

procedure {:yields} {:layer 1} {:refines "put_spec"} put(args: ArgList)
  returns (rets: ArgList)
  requires {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
  requires {:layer 1} 0 <= args[0] && args[0] < tabLen;
  ensures {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
{
  var {:linear "this"} this: Invoc;
  var {:layer 1} my_vis: Set;

  var k: int;
  var v: int;

  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
  call this := History.call(Map.put, args);
  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h) && History.pending(h, this);

  k := args[0];
  v := args[1];

  call writeTable(k, v);

  call intro_add_tabvis(k, this);
  call my_vis := intro_read_tabvis_range(0, tabLen);
  call intro_write_vis(this, my_vis);
  call intro_writeAbs(k, v);
  call intro_writeLin(this);

  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h)
    && History.pending(h, this) && Seq.elem(this, lin);
  call History.return(this, rets);
  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
}

procedure {:yields} {:layer 1} {:refines "get_spec"} get(args: ArgList)
  returns (rets: ArgList)
  requires {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
  requires {:layer 1} 0 <= args[0] && args[0] < tabLen;
  ensures {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
{
  var {:linear "this"} this: Invoc;
  var {:layer 1} my_vis: Set;

  var k: int;
  var v: int;

  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
  call this := History.call(Map.get, args);
  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h) && History.pending(h, this);

  k := args[0];

  call v := readTable(k);
  rets[0] := v;

  call intro_add_tabvis(k, this);
  call my_vis := intro_read_tabvis_range(0, tabLen);
  call intro_write_vis(this, my_vis);
  call intro_writeLin(this);

  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h)
    && History.pending(h, this) && Seq.elem(this, lin);
  call History.return(this, rets);
  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
}

procedure {:yields} {:layer 1} {:refines "contains_spec"} contains(args: ArgList)
  returns (rets: ArgList)
  requires {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
  ensures {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
{
  var k, tv: int;
  var {:linear "this"} this: Invoc;
  var {:layer 1} my_vis, my_vis1: Set;

  var v: int;
  var res: bool;
  var witness_k: int;

  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
  call this := History.call(Map.contains, args);
  assume tabLen - 1 == Map.key(this);
  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h) && History.pending(h, this);

  v := args[0];

  k := 0;
  my_vis := Set.empty;

  while (k < tabLen)
    invariant {:layer 1} 0 <= k && k <= tabLen;
    invariant {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h) && History.pending(h, this);
    invariant {:layer 1} (forall i: int :: 0 <= i && i < k ==> Map.ofVis(my_vis, lin)[i] != v);
    invariant {:layer 1} Set.subset(my_vis, Set.ofSeq(lin));
    invariant {:layer 1} (forall n1 : Invoc :: Set.elem(n1, my_vis) ==> Set.elem(n1, tabvis[Map.key(n1)]));
    invariant {:layer 1} (forall n1 : Invoc :: Set.elem(n1, my_vis) ==> 0 <= Map.key(n1) && Map.key(n1) < k);
    invariant {:layer 1} (forall n1, n2: Invoc ::
                          hb(n1, this) && Set.elem(n2, vis[n1])
                          && 0 <= Map.key(n2) && Map.key(n2) < k
                          ==> Set.elem(n2, my_vis));
  {
    // Read table[k] and add tabvis[k] to my_vis
    call tv := readTable(k);

    call my_vis1 := intro_read_tabvis(k);
    call lemma_state_Set.union(k, tabLen, my_vis, my_vis1);
    my_vis := Set.union(my_vis, my_vis1);

    if (tv == v) {
      // Linearization point
      call my_vis1 := intro_read_tabvis_range(k+1, tabLen);
      assert {:layer 1} (forall n1, n2: Invoc ::
                          hb(n1, this) && Set.elem(n2, vis[n1])
                          && 0 <= Map.key(n2) && Map.key(n2) < k+1
                          ==> Set.elem(n2, my_vis));
      call lemma_state_Set.union(k+1, tabLen, my_vis, my_vis1);
      my_vis := Set.union(my_vis, my_vis1);
      call intro_write_vis(this, my_vis);
      call intro_add_tabvis(tabLen-1, this);
      call intro_writeLin(this);
      witness_k := k;

      res := true;

      rets[0] := Value.ofBool(res);
      rets[1] := witness_k;

      yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h)
        && History.pending(h, this) && Seq.elem(this, lin);
      call History.return(this, rets);
      yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
      return;
    }
    k := k + 1;
    yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h) && History.pending(h, this)
      && (forall i: int :: 0 <= i && i < k ==> Map.ofVis(my_vis, lin)[i] != v)
      && Set.subset(my_vis, Set.ofSeq(lin))
      && (forall n1 : Invoc :: Set.elem(n1, my_vis) ==> Set.elem(n1, tabvis[Map.key(n1)]))
      && (forall n1 : Invoc :: Set.elem(n1, my_vis) ==> 0 <= Map.key(n1) && Map.key(n1) < k);
      assert {:layer 1} (forall n1, n2: Invoc :: hb(n1, this) && Set.elem(n2, vis[n1])
         && 0 <= Map.key(n2) && Map.key(n2) < k ==> Set.elem(n2, my_vis));
  }
  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h) && History.pending(h, this)
    && (forall i: int :: 0 <= i && i < tabLen ==> Map.ofVis(my_vis, lin)[i] != v)
    && (forall n1 : Invoc :: Set.elem(n1, my_vis) ==> Set.elem(n1, tabvis[Map.key(n1)]))
    && (forall n1 : Invoc :: Set.elem(n1, my_vis) ==> 0 <= Map.key(n1) && Map.key(n1) < tabLen)
    && (forall n1, n2: Invoc :: hb(n1, this) && Set.elem(n2, vis[n1])
                         && 0 <= Map.key(n2) && Map.key(n2) < k
                         ==> Set.elem(n2, my_vis));

  // Linearization point
  call intro_write_vis(this, my_vis);
  call intro_add_tabvis(tabLen-1, this);
  call intro_writeLin(this);
  witness_k := k;

  res := false;

  rets[0] := Value.ofBool(res);
  rets[1] := witness_k;

  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h)
    && History.pending(h, this) && Seq.elem(this, lin);
  call History.return(this, rets);
  yield; assert {:layer 1} tableInv(table, tabLen, tabvis, abs, lin, vis, h);
  return;
}
