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
      call intro_add_tabvis(tabLen-1, this);
      call Consistency.linPoint(this);
      call Consistency.setVis(this, my_vis);
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
  call intro_add_tabvis(tabLen-1, this);
  call Consistency.linPoint(this);
  call Consistency.setVis(this, my_vis);
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
