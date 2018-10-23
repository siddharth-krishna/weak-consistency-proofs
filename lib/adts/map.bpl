/**
 * The key-value map ADT.
 */

/**
 * Exported declarations
 */

const unique Map.get, Map.put, Map.contains: Method;
type Map.State = [int] int;
function Map.key(n: Invoc): int;
function Map.value(n: Invoc): int;

// A function to calculate the abstract state after executing a subset vis of
// a sequence of invocations lin
function Map.ofVis(vis: Set, lin: Seq): Map.State;

// TODO define this one directly instead of Map.ofVis
function Map.ofSeq(seq: Seq): Map.State;

// A function to Map.restrict a Set to invocations involving key ke
function Map.restr(s: Set, k: int): Set;

// Union of disjoint keys means state comes from one of the two sets
procedure {:layer 1} lemma_state_Set.union(k: int, K: int, s, t: Set);
  requires (forall n: Invoc :: Set.elem(n, s) ==> Map.key(n) < k);
  requires (forall n: Invoc :: Set.elem(n, t) ==> k <= Map.key(n));
  ensures (forall i: int :: 0 <= i && i < k ==>
    Map.ofVis(Set.union(s, t), lin)[i] == Map.ofVis(s, lin)[i]);
  ensures (forall i: int :: k <= i && i < K ==>
    Map.ofVis(Set.union(s, t), lin)[i] == Map.ofVis(t, lin)[i]);

/**
 * Internal declarations
 */

axiom (forall n: Invoc :: Invoc.name(n) == Map.put ==> Map.key(n) == Invoc.args(n)[0]);
axiom (forall n: Invoc :: Invoc.name(n) == Map.put ==> Map.value(n) == Invoc.args(n)[1]);
axiom (forall n: Invoc :: Invoc.name(n) == Map.get ==> Map.key(n) == Invoc.args(n)[0]);
axiom (forall n: Invoc :: Invoc.name(n) == Map.contains ==> Map.value(n) == Invoc.args(n)[0]);

// Map.restr is a subset
axiom (forall s: Set, k: int :: Set.subset(Map.restr(s, k), s));

// Map.restr is monotonic w.r.t subset
axiom (forall s, t: Set, k: int :: Set.subset(s, t) ==> Set.subset(Map.restr(s, k), Map.restr(t, k)));

// Adding an invocation on k increases Map.restr
axiom (forall q: Seq, n: Invoc :: {Map.restr(Set.ofSeq(Seq.append(q, n)), Map.key(n))}
        Map.restr(Set.ofSeq(Seq.append(q, n)), Map.key(n))
          == Set.add(Map.restr(Set.ofSeq(q), Map.key(n)), n));

// Adding invocations not on k preserves Map.restr
axiom (forall q: Seq, n: Invoc, k: int :: Map.key(n) != k
       ==> Map.restr(Set.ofSeq(Seq.append(q, n)), k) == Map.restr(Set.ofSeq(q), k));

// The effect of appending an invocation on key k on state of k
axiom (forall s1, s2: Set, q1, q2: Seq, n: Invoc ::
       q2 == Seq.append(q1, n) && s2 == Set.add(s1, n)
       ==> (Invoc.name(n) == Map.put ==> Map.ofVis(s2, q2)[Map.key(n)] == Map.value(n)));

// Appending a get/contains invocation does not change state
axiom (forall s1, s2: Set, q1, q2: Seq, n: Invoc, k: int ::
       q2 == Seq.append(q1, n) && s2 == Set.add(s1, n)
       && (Invoc.name(n) == Map.get || Invoc.name(n) == Map.contains)
       ==> Map.ofVis(s2, q2)[k] == Map.ofVis(s1, q1)[k]);

// The effect of appending an invocation on key k on state with unchanged vis
axiom (forall s: Set, q1: Seq, n: Invoc, k: int ::
          Map.ofVis(s, q1)[k] == Map.ofVis(s, Seq.append(q1, n))[k]);

// The mapping of key k depends only invocations involving k
axiom (forall s: Set, q: Seq, k: int ::
        Map.ofVis(s, q)[k] == Map.ofVis(Map.restr(s, k), q)[k]);
axiom (forall q: Seq, k: int ::
        Map.ofVis(Set.ofSeq(q), q)[k] == Map.ofVis(Map.restr(Set.ofSeq(q), k), q)[k]);

// Taking union with a Map.restriction of a super-set means Map.restrictions are same
axiom (forall s0, s1, t: Set, k: int ::
        s1 == Set.union(s0, t) && Set.subset(Map.restr(s0, k), t) ==>
          Map.restr(s1, k) == Map.restr(t, k)
);
