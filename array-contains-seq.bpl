// A simplified hash table implementation with weakly consistent contains method


// ---------- Encoding of weak visibility

type Invoc;

// Create an invocation. Methods are: 0 - put, 1 - get, 2 - contains
function createInvoc(m: int, k: int, v: int) returns (i: Invoc);


type SeqInvoc;  // sequence of invocations


function subseq(s: SeqInvoc, t: SeqInvoc) : bool;

// subseq is reflexive
axiom (forall s: SeqInvoc :: subseq(s, s));

// subseq is transitive
axiom (forall s, t, u: SeqInvoc :: subseq(s, t) && subseq(t, u) ==> subseq(s, u));


function append(s: SeqInvoc, o: Invoc) returns (t: SeqInvoc);

// append preserves subseq
axiom (forall s, t: SeqInvoc, o: Invoc :: subseq(s, t) ==> subseq(append(s, o), append(t, o)));


function union(s1: SeqInvoc, s2: SeqInvoc) returns (t: SeqInvoc);

// union is idempotent
axiom (forall s: SeqInvoc :: s == union(s, s));

// union is associative
axiom (forall s, t: SeqInvoc :: union(s, t) == union(t, s));

// union is monotonic w.r.t subseq
axiom (forall s, t1, t2: SeqInvoc :: subseq(t1, t2) ==> subseq(union(s, t1), union(s, t2)));


// A function to restrict a SeqInvoc to invocations involving key k
function restr(s: SeqInvoc, k: int) returns (t: SeqInvoc);

// restr is a subseq
axiom (forall s: SeqInvoc, k: int :: subseq(restr(s, k), s));


// A function to calculate the abstract state after a sequential execution
function state(s: SeqInvoc) returns (m: [int]int);

// The mapping of key k depends only invocations involving k
axiom (forall s: SeqInvoc, k: int :: state(s)[k] == state(restr(s, k))[k]);

// Adding invocations of a key k does not affect state of keys k1 != k
axiom (forall s, t: SeqInvoc, k, k1: int :: k != k1 ==> state(union(s, restr(t, k)))[k1] == state(s)[k1]);


// ---------- Some lemmas that we need

procedure lemma_append_effect(s1, s2: SeqInvoc, o: Invoc, m, k, v: int)
  requires s2 == append(s1, o) && o == createInvoc(m, k, v);
  ensures (forall i: int :: i != k ==> state(s1)[i] == state(s2)[i]);
  ensures m == 0 ==> state(s2)[k] == v;
  ensures m == 1 || m == 2 ==> state(s2)[k] == state(s1)[k];
{
  assume false;
}

procedure lemma_union_restr(s0, s1, t: SeqInvoc, k: int)
  requires s1 == union(s0, restr(t, k)) && subseq(s0, t);
  ensures restr(s1, k) == restr(t, k);
{
  assume false;
}


// ---------- Logical and concrete shared state

var lin: SeqInvoc;  // a shared global variable that builds the linearization
// Need to restrict actions/interference to only increase lin

// Concrete state of implementation
var table: [int]int;
const tableLen: int;
axiom 0 <= tableLen;


// ---------- Procedures/methods

procedure put(k: int, v: int)
  modifies table, lin;
  requires 0 <= k && k < tableLen;
  requires (forall i: int :: 0 <= i && i < tableLen ==> table[i] == state(lin)[i]);
  ensures (forall i: int :: 0 <= i && i < tableLen ==> table[i] == state(lin)[i]);
{
  var old_lin: SeqInvoc;
  var invoc: Invoc;

  table[k] := v;

  old_lin := lin;
  invoc := createInvoc(0, k, v);
  lin := append(lin, invoc);
  call lemma_append_effect(old_lin, lin, invoc, 0, k, v);
}

procedure get(k: int) returns (v: int)
  modifies lin;
  requires 0 <= k && k < tableLen;
  requires (forall i: int :: 0 <= i && i < tableLen ==> table[i] == state(lin)[i]);
  ensures (forall i: int :: 0 <= i && i < tableLen ==> table[i] == state(lin)[i]);
{
  var old_lin: SeqInvoc;
  var invoc: Invoc;
  v := table[k];

  old_lin := lin;
  invoc := createInvoc(1, k, v);
  lin := append(lin, invoc);
  call lemma_append_effect(old_lin, lin, invoc, 1, k, v);
}

procedure contains(v: int) returns (res: bool, vis: SeqInvoc, witness_k: int)
  modifies lin;
  requires (forall i: int :: 0 <= i && i < tableLen ==> table[i] == state(lin)[i]);
  ensures (forall i: int :: 0 <= i && i < tableLen ==> table[i] == state(lin)[i]);
  ensures subseq(vis, lin);
  ensures res ==> state(vis)[witness_k] == v;
  ensures !res ==> (forall i: int :: 0 <= i && i < tableLen ==> state(vis)[i] != v);
{
  var invoc: Invoc;
  var old_lin, old_vis: SeqInvoc;
  var k, tv: int;

  vis := lin;  // Need to show forall j in hb :: j.vis subsetof vis
  assert subseq(vis, lin);

  k := 0;
  while (k < tableLen)
    invariant 0 <= k && k <= tableLen;
    invariant subseq(vis, lin);
    invariant (forall i: int :: 0 <= i && i < k ==> state(vis)[i] != v);
    invariant (forall i: int :: 0 <= i && i < tableLen ==> table[i] == state(lin)[i]);
  {
    tv := table[k];

    old_vis := vis;
    vis := union(vis, restr(lin, k));
    call lemma_union_restr(old_vis, vis, lin, k);
    // tv == table[k] == state(lin)[k] == state(restr(lin, k))[k]
    // == state(restr(vis, k))[k] == state(vis)[k]
    assert tv == state(vis)[k];
    // also, restr(lin, k) subseq lin ==> vis subseq lin
    assert subseq(union(old_vis, restr(lin, k)), union(old_vis, lin));
    assert subseq(union(old_vis, lin), union(lin, lin));
    assert subseq(vis, lin);

    if (tv == v) {
      assert state(vis)[k] == v;
      invoc := createInvoc(2, k, v);
      old_lin := lin;
      old_vis := vis;
      lin := append(lin, invoc);
      vis := append(vis, invoc);
      call lemma_append_effect(old_lin, lin, invoc, 2, k, v);
      call lemma_append_effect(old_vis, vis, invoc, 2, k, v);
      witness_k := k;

      res := true;
      return;
    }
    // else tv != table[k] == state(lin)[k] == state(restr(lin, k))[k] == state(restr(vis, k))[k] == state(vis)[k]
    k := k + 1;
  }
  invoc := createInvoc(2, k, v);
  old_lin := lin;
  old_vis := vis;
  lin := append(lin, invoc);
  vis := append(vis, invoc);
  call lemma_append_effect(old_lin, lin, invoc, 2, k, v);
  call lemma_append_effect(old_vis, vis, invoc, 2, k, v);

  res := false;
  return;
}
