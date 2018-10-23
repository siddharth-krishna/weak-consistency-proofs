/**
 * Exported declarations
 */

type Method;
type Invoc;
type Value = int;
type ArgList = [int] Value;

function Invoc.name(i: Invoc): Method;
function Invoc.args(i: Invoc): ArgList;
function Invoc.rets(i: Invoc): ArgList;

// Sequences of invocations
type Seq;
function Seq.append(s: Seq, o: Invoc): Seq;
function Seq.elem(n: Invoc, s: Seq): bool;

// Sets of invocations
type Set;
const Set.empty: Set;
function Set.elem(n: Invoc, s: Set): bool;
function Set.subset(s: Set, t: Set): bool;
function Set.union(s1: Set, s2: Set): Set;
function Set.unionAll(m: [int] Set, i: int, j: int): Set;
function Set.ofSeq(q: Seq): Set;
function Set.add(s: Set, n: Invoc): Set;
function Set.addAll(m: [int] Set, n: Invoc, i: int, j: int): [int] Set;

/**
 * Internal declarations
 */

// Boilerplate stuff for linear variables
function {:builtin "MapConst"} MapConstBool(bool): [Invoc] bool;
function {:inline} {:linear "this"} InvocCollector(x: Invoc): [Invoc] bool
{
  MapConstBool(false)[x := true]
}

// Relationship between elem and append
axiom (forall n1, n2: Invoc, s: Seq :: {Seq.elem(n1, Seq.append(s, n2))}
       Seq.elem(n1, s) ==> Seq.elem(n1, Seq.append(s, n2)));

axiom (forall n: Invoc, s: Seq :: {Seq.elem(n, Seq.append(s, n))}
       Seq.elem(n, Seq.append(s, n)));

// Set.empty is a subset of anything
axiom (forall s: Set :: Set.subset(Set.empty, s));

// Nothing is an elem of Set.empty
axiom (forall n: Invoc :: !Set.elem(n, Set.empty));

// subset is reflexive
axiom (forall s: Set :: Set.subset(s, s));

// subset is transitive
axiom (forall s, t, u: Set :: Set.subset(s, t) && Set.subset(t, u) ==> Set.subset(s, u));

// definition of subset in terms of elem
axiom (forall s, t: Set :: (forall n: Invoc :: Set.elem(n, s) ==> Set.elem(n, t)) ==> Set.subset(s, t));

// union is idempotent
axiom (forall s: Set :: s == Set.union(s, s));

// union is associative
axiom (forall s, t: Set :: Set.union(s, t) == Set.union(t, s));

// union is monotonic w.r.t subset
axiom (forall s, t1, t2: Set :: Set.subset(t1, t2) ==> Set.subset(Set.union(s, t1), Set.union(s, t2)));

axiom (forall s, t1, t2: Set :: Set.subset(t1, s) && Set.subset(t2, s) ==> Set.subset(Set.union(t1, t2), s));

// relation between union and elem
axiom (forall n: Invoc, s, t: Set :: Set.elem(n, s) ==> Set.elem(n, Set.union(s, t)));

// Relation between add and elem
axiom (forall s: Set, n1, n2: Invoc :: Set.elem(n1, Set.add(s, n2))
       ==> n1 == n2 || Set.elem(n1, s));
axiom (forall s: Set, n1, n2: Invoc :: Set.elem(n1, s) ==> Set.elem(n1, Set.add(s, n2)));

// Relation between union and elem
axiom (forall s, t: Set, n1: Invoc :: Set.elem(n1, Set.union(s, t))
       ==> Set.elem(n1, s) || Set.elem(n1, t));

// add preserves subset relation
axiom (forall s, t: Set, n: Invoc :: Set.subset(s, t) ==> Set.subset(Set.add(s, n), Set.add(t, n)));
axiom (forall s, t: Set, n: Invoc :: Set.subset(s, t) ==> Set.subset(s, Set.add(t, n)));

// Relation between setOfSeq, add, and append
axiom (forall q: Seq, n: Invoc :: Set.ofSeq(Seq.append(q, n)) == Set.add(Set.ofSeq(q), n));

// Relation between unionAll, add, and append
axiom (forall t: [int]Set, i, j, k: int, q: Seq, n: Invoc ::
        Set.unionAll(t, i, j) == Set.ofSeq(q) && i <= k && k < j
        ==> Set.unionAll(t[k := Set.add(t[k], n)], i, j) == Set.ofSeq(Seq.append(q, n)));

// The effect of Set.addAll
axiom (forall m: [int]Set, n: Invoc, i: int, j: int, k: int ::
        i <= k && k < j ==> Set.addAll(m, n, i, j)[k] == Set.add(m[k], n));
axiom (forall m: [int]Set, n: Invoc, i: int, j: int, k: int ::
        !(i <= k && k < j) ==> Set.addAll(m, n, i, j)[k] == m[k]);

// What happens to unionAll and setOfSeq when you do an Set.addAll
axiom (forall t: [int]Set, i, j, i1, j1: int, q: Seq, n: Invoc ::
        Set.unionAll(t, i, j) == Set.ofSeq(q) && i <= i1 && i1 < j1 && j1 <= j ==>
          Set.unionAll(Set.addAll(t, n, i1, j1), i, j) == Set.ofSeq(Seq.append(q, n)));
