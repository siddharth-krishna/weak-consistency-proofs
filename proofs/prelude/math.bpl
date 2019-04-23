// ----------------------------------------
// Mathematical sets, sequences, etc.
// 
// ----------------------------------------


// ---------- Types and axiomatization of sets

// Sets of invocations
type SetInvoc;

const Set_empty: SetInvoc;

function Set(n: Invoc) : SetInvoc;  // singleton set

function Set_elem(n: Invoc, s: SetInvoc) : bool;

function Set_subset(s: SetInvoc, t: SetInvoc) : bool;

function Set_equal(s, t: SetInvoc) : bool;  // helper function to prove sets are equal

// extensionality
axiom (forall s, t: SetInvoc :: {Set_equal(s, t)}
  (forall n: Invoc :: Set_elem(n, s) <==> Set_elem(n, t)) ==> Set_equal(s, t) && s == t);

// Set_empty is a subset of anything
axiom (forall s: SetInvoc :: Set_subset(Set_empty, s));

// Nothing is an elem of Set_empty
axiom (forall n: Invoc :: !Set_elem(n, Set_empty));

// Set(n) definition
axiom (forall n1, n2: Invoc :: {Set_elem(n2, Set(n1))}
  Set_elem(n2, Set(n1)) <==> n2 == n1);

// subset is reflexive
axiom (forall s: SetInvoc :: Set_subset(s, s));

// subset is transitive
axiom (forall s, t, u: SetInvoc ::
    {Set_subset(s, t), Set_subset(t, u), Set_subset(s, u)}
  Set_subset(s, t) && Set_subset(t, u) ==> Set_subset(s, u));

// definition of subset in terms of elem
axiom (forall s, t: SetInvoc :: {Set_subset(s, t)}
  (forall n: Invoc :: Set_elem(n, s) ==> Set_elem(n, t)) ==> Set_subset(s, t));
axiom (forall s, t: SetInvoc, n: Invoc ::
    {Set_subset(s, t), Set_elem(n, s)} {Set_subset(s, t), Set_elem(n, t)}
  Set_subset(s, t) && Set_elem(n, s) ==> Set_elem(n, t));

function Set_union(s1: SetInvoc, s2: SetInvoc) returns (t: SetInvoc);

// union is idempotent
axiom (forall s: SetInvoc :: s == Set_union(s, s));

// union is associative
axiom (forall s, t: SetInvoc :: {Set_union(s, t), Set_union(t, s)}
  Set_union(s, t) == Set_union(t, s));

// union preserves subset
axiom (forall s1, s2, s3: SetInvoc :: {Set_subset(s1, s2), Set_subset(s1, Set_union(s2, s3))}
  Set_subset(s1, s2) ==> Set_subset(s1, Set_union(s2, s3)));

// union with empty
axiom (forall s: SetInvoc :: Set_union(s, Set_empty) == s);
axiom (forall s: SetInvoc :: Set_union(Set_empty, s) == s);

// union is monotonic w.r.t subset
// axiom (forall s, t1, t2: SetInvoc ::
//   Set_subset(t1, t2) ==> Set_subset(Set_union(s, t1), Set_union(s, t2)));

// axiom (forall s, t1, t2: SetInvoc ::
//   Set_subset(t1, s) && Set_subset(t2, s) ==> Set_subset(Set_union(t1, t2), s));

// relation between union and elem
axiom (forall n: Invoc, s, t: SetInvoc ::
    {Set_elem(n, Set_union(s, t)), Set_elem(n, t)}
    {Set_elem(n, Set_union(s, t)), Set_elem(n, s)}
  Set_elem(n, Set_union(s, t)) <==> Set_elem(n, s) || Set_elem(n, t));

// intersection
function Set_inter(s1: SetInvoc, s2: SetInvoc) returns (t: SetInvoc);

// relation between intersection and elem
axiom (forall n: Invoc, s, t: SetInvoc ::
    {Set_elem(n, Set_inter(s, t)), Set_elem(n, t)}
    {Set_elem(n, Set_inter(s, t)), Set_elem(n, s)}
  Set_elem(n, Set_inter(s, t)) <==> Set_elem(n, s) && Set_elem(n, t));

// intersection with empty
axiom (forall s: SetInvoc :: Set_inter(s, Set_empty) == Set_empty);
axiom (forall s: SetInvoc :: Set_inter(Set_empty, s) == Set_empty);

function Set_ofSeq(q: SeqInvoc) returns (s: SetInvoc);

function Set_add(s: SetInvoc, n: Invoc) returns (t: SetInvoc);

// add in terms of union and singleton
axiom (forall s: SetInvoc, n: Invoc :: {Set_union(s, Set(n))} Set_add(s, n) == Set_union(s, Set(n)));

// Relation between add and elem
axiom (forall s: SetInvoc, n1, n2: Invoc :: {Set_elem(n1, Set_add(s, n2))}
  Set_elem(n1, Set_add(s, n2)) <==> n1 == n2 || Set_elem(n1, s));
axiom (forall s: SetInvoc, n: Invoc :: {Set_elem(n, s), Set_add(s, n)}
  Set_elem(n, s) ==> Set_add(s, n) == s);

// What happens when you add to empty
axiom (forall n: Invoc :: {Set_add(Set_empty, n)} Set_add(Set_empty, n) == Set(n));

// Relation between union and elem
// axiom (forall s, t: SetInvoc, n1: Invoc :: Set_elem(n1, Set_union(s, t))
//        ==> Set_elem(n1, s) || Set_elem(n1, t));

// add preserves subset relation
// axiom (forall s, t: SetInvoc, n: Invoc :: Set_subset(s, t) ==> Set_subset(Set_add(s, n), Set_add(t, n)));
axiom (forall s, t: SetInvoc, n: Invoc :: {Set_subset(s, Set_add(t, n))}
  Set_subset(s, t) ==> Set_subset(s, Set_add(t, n)));


// ---------- Types and axiomatization of sequences (of invocations)

// Sequences of invocations
type SeqInvoc;

function Seq_append(s: SeqInvoc, o: Invoc) returns (t: SeqInvoc);

function Seq_elem(n: Invoc, s: SeqInvoc) : bool;

// Relationship between elem and append
axiom (forall n1, n2: Invoc, s: SeqInvoc :: {Seq_elem(n1, Seq_append(s, n2))}
       Seq_elem(n1, Seq_append(s, n2)) <==> Seq_elem(n1, s) || n1 == n2);


// Relation between Set_ofSeq, add, and append
axiom (forall q: SeqInvoc, n: Invoc :: {Set_ofSeq(Seq_append(q, n))}
  Set_ofSeq(Seq_append(q, n)) == Set_add(Set_ofSeq(q), n));

// Relation between Set_ofSeq, Set_elem, and Seq_elem
axiom (forall q: SeqInvoc, n: Invoc :: {Set_elem(n, Set_ofSeq(q))}
  Seq_elem(n, q) <==> Set_elem(n, Set_ofSeq(q)));


// Distinct sequences
function Seq_distinct(q: SeqInvoc) : bool;

axiom (forall q: SeqInvoc, n: Invoc :: {Seq_distinct(Seq_append(q, n))}
  Seq_distinct(q) && !Seq_elem(n, q) ==> Seq_distinct(Seq_append(q, n)));


// Seq_restr(q, s) = sequence obtained by restricting q to s
function Seq_restr(q: SeqInvoc, s: SetInvoc) : SeqInvoc;

// The identity restriction
axiom (forall q: SeqInvoc :: {Seq_restr(q, Set_ofSeq(q))}
  Seq_restr(q, Set_ofSeq(q)) == q);

// Effect of appending new element on restriction
axiom (forall q: SeqInvoc, s: SetInvoc, n: Invoc :: {Seq_restr(Seq_append(q, n), s)}
  Seq_distinct(Seq_append(q, n)) && Set_subset(s, Set_ofSeq(q))
  ==> Seq_restr(Seq_append(q, n), s) == Seq_restr(q, s));
axiom (forall q: SeqInvoc, s: SetInvoc, n: Invoc ::
    {Seq_restr(Seq_append(q, n), Set_add(s, n))}
  Seq_distinct(Seq_append(q, n)) && !Set_elem(n, s)
  ==> Seq_restr(Seq_append(q, n), Set_add(s, n)) == Seq_append(Seq_restr(q, s), n));

// Relation between Seq_elem and Seq_restr
axiom (forall q: SeqInvoc, s: SetInvoc, n: Invoc :: {Seq_elem(n, Seq_restr(q, s))}
  Seq_elem(n, Seq_restr(q, s)) <==> Seq_elem(n, q) && Set_elem(n, s));


// Implicit (strict) order of a sequence
function Seq_ord(q: SeqInvoc, n1, n2: Invoc) : bool;

// This order is transitive
// axiom (forall q: SeqInvoc, n1, n2, n3: Invoc :: //{}
//   Seq_ord(q, n1, n2) && Seq_ord(q, n2, n3) ==> Seq_ord(q, n1, n3));

// Adding to the restriction set is append if ordered correctly
axiom (forall q: SeqInvoc, s: SetInvoc, n: Invoc ::
    {Seq_append(Seq_restr(q, s), n)}
  (forall n1: Invoc :: Seq_elem(n1, Seq_restr(q, s)) ==> Seq_ord(q, n1, n))
  && Seq_elem(n, q) && !Set_elem(n, s)
  ==> Seq_restr(q, Set_add(s, n)) == Seq_append(Seq_restr(q, s), n));

// Appending extends order
axiom (forall q: SeqInvoc, n, n1, n2: Invoc :: {Seq_ord(Seq_append(q, n), n1, n2)}
  Seq_distinct(q) ==>
  (Seq_ord(Seq_append(q, n), n1, n2)
    <==> (Seq_elem(n1, q) && Seq_elem(n2, q) && Seq_ord(q, n1, n2))
      || (Seq_elem(n1, q) && n2 == n)));
