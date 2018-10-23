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
