// ----------------------------------------
//
// The key-value map Abstract Data Type
// 
// ----------------------------------------


const unique Map.get, Map.put, Map.contains: Method;

function invoc_m(n: Invoc) : Method;
function invoc_k(n: Invoc) : int;
function invoc_v(n: Invoc) : int;

type Map.State = [int]int; // Abstract state

function Map.ofSeq(s: SeqInvoc) : Map.State;


// ---------- Axioms of the map ADT

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
  modifies abs, lin, vis;
{
  var my_vis: SetInvoc;

  // Satisfies its functional spec
  assume true;
  abs[k] := v;

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
  v := abs[k];

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

