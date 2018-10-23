/**
 * The key-value map ADT.
 */

const unique get, put, contains: Method;

function Map.key(n: Invoc): int;
function Map.value(n: Invoc): int;

axiom (forall n: Invoc :: Invoc.name(n) == put ==> Map.key(n) == Invoc.args(n)[0]);
axiom (forall n: Invoc :: Invoc.name(n) == put ==> Map.value(n) == Invoc.args(n)[1]);
axiom (forall n: Invoc :: Invoc.name(n) == get ==> Map.key(n) == Invoc.args(n)[0]);
axiom (forall n: Invoc :: Invoc.name(n) == contains ==> Map.value(n) == Invoc.args(n)[0]);

// A function to restrict a Set to invocations involving key ke
function restr(s: Set, k: int) returns (t: Set);

// restr is a subset
axiom (forall s: Set, k: int :: Set.subset(restr(s, k), s));

// restr is monotonic w.r.t subset
axiom (forall s, t: Set, k: int :: Set.subset(s, t) ==> Set.subset(restr(s, k), restr(t, k)));

// Adding an invocation on k increases restr
axiom (forall q: Seq, n: Invoc :: {restr(Set.ofSeq(Seq.append(q, n)), Map.key(n))}
        restr(Set.ofSeq(Seq.append(q, n)), Map.key(n))
          == Set.add(restr(Set.ofSeq(q), Map.key(n)), n));

// Adding invocations not on k preserves restr
axiom (forall q: Seq, n: Invoc, k: int :: Map.key(n) != k
       ==> restr(Set.ofSeq(Seq.append(q, n)), k) == restr(Set.ofSeq(q), k));

type AbsState = [int]int; // Abstract state

// A function to calculate the abstract state after executing a subset vis of
// a sequence of invocations lin
function state(vis: Set, lin: Seq) returns (m: AbsState);


// The effect of appending an invocation on key k on state of k
axiom (forall s1, s2: Set, q1, q2: Seq, n: Invoc ::
       q2 == Seq.append(q1, n) && s2 == Set.add(s1, n)
       ==> (Invoc.name(n) == put ==> state(s2, q2)[Map.key(n)] == Map.value(n)));

// Appending a get/contains invocation does not change state
axiom (forall s1, s2: Set, q1, q2: Seq, n: Invoc, k: int ::
       q2 == Seq.append(q1, n) && s2 == Set.add(s1, n)
       && (Invoc.name(n) == get || Invoc.name(n) == contains)
       ==> state(s2, q2)[k] == state(s1, q1)[k]);

// The effect of appending an invocation on key k on state with unchanged vis
axiom (forall s: Set, q1: Seq, n: Invoc, k: int ::
          state(s, q1)[k] == state(s, Seq.append(q1, n))[k]);


// The mapping of key k depends only invocations involving k
axiom (forall s: Set, q: Seq, k: int ::
        state(s, q)[k] == state(restr(s, k), q)[k]);
axiom (forall q: Seq, k: int ::
        state(Set.ofSeq(q), q)[k] == state(restr(Set.ofSeq(q), k), q)[k]);

// Taking union with a restriction of a super-set means restrictions are same
axiom (forall s0, s1, t: Set, k: int ::
        s1 == Set.union(s0, t) && Set.subset(restr(s0, k), t) ==>
          restr(s1, k) == restr(t, k)
);

// Union of disjoint keys means state comes from one of the two sets
procedure {:layer 1} lemma_state_Set.union(k: int, K: int, s, t: Set);
  requires (forall n: Invoc :: Set.elem(n, s) ==> Map.key(n) < k);
  requires (forall n: Invoc :: Set.elem(n, t) ==> k <= Map.key(n));
  ensures (forall i: int :: 0 <= i && i < k ==>
    state(Set.union(s, t), lin)[i] == state(s, lin)[i]);
  ensures (forall i: int :: k <= i && i < K ==>
    state(Set.union(s, t), lin)[i] == state(t, lin)[i]);
