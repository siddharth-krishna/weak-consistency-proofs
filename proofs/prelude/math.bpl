// ----------------------------------------
// Mathematical sets, sequences, etc.
//
// These axioms are adapted from Dafny's axioms,
// instantiated to type Invoc because CIVL does not support polymorphic Boogie:
// https://github.com/boogie-org/boogie/issues/122
//
// The dafny axioms were taken from
// https://github.com/Microsoft/dafny/blob/master/Binaries/DafnyPrelude.bpl
// which had the following notice at the top of the file:
// Dafny prelude
// Created 9 February 2008 by Rustan Leino.
// Converted to Boogie 2 on 28 June 2008.
// Edited sequence axioms 20 October 2009 by Alex Summers.
// Modified 2014 by Dan Rosen.
// Copyright (c) 2008-2014, Microsoft.
// ----------------------------------------


// ---------- Types and axiomatization of sets (of invocations)

type SetInvoc = [Invoc]bool;

function Set_card(SetInvoc): int;
axiom (forall s: SetInvoc :: { Set_card(s) } 0 <= Set_card(s));

function Set_empty(): SetInvoc;
axiom (forall o: Invoc :: { Set_empty()[o] } !Set_empty()[o]);
axiom (forall s: SetInvoc :: { Set_card(s) }
  (Set_card(s) == 0 <==> s == Set_empty()) &&
  (Set_card(s) != 0 ==> (exists x: Invoc :: s[x])));

// the empty set could be of anything
//axiom (forall t: Ty :: { $Is(Set_empty() : [Invoc]bool, TSet(t)) } $Is(Set_empty() : [Invoc]bool, TSet(t)));

function Set(Invoc): SetInvoc;
axiom (forall r: Invoc :: { Set(r) } Set(r)[r]);
axiom (forall r: Invoc, o: Invoc :: { Set(r)[o] } Set(r)[o] <==> r == o);
axiom (forall r: Invoc :: { Set_card(Set(r)) } Set_card(Set(r)) == 1);

function Set_add(SetInvoc, Invoc): SetInvoc;
axiom (forall a: SetInvoc, x: Invoc, o: Invoc :: { Set_add(a,x)[o] }
  Set_add(a,x)[o] <==> o == x || a[o]);
axiom (forall a: SetInvoc, x: Invoc :: { Set_add(a, x) }
  Set_add(a, x)[x]);
axiom (forall a: SetInvoc, x: Invoc, y: Invoc :: { Set_add(a, x), a[y] }
  a[y] ==> Set_add(a, x)[y]);
axiom (forall a: SetInvoc, x: Invoc :: { Set_card(Set_add(a, x)) }
  a[x] ==> Set_card(Set_add(a, x)) == Set_card(a));
axiom (forall a: SetInvoc, x: Invoc :: { Set_card(Set_add(a, x)) }
  !a[x] ==> Set_card(Set_add(a, x)) == Set_card(a) + 1);

function Set_union(SetInvoc, SetInvoc): SetInvoc;
axiom (forall a: SetInvoc, b: SetInvoc, o: Invoc :: { Set_union(a,b)[o] }
  Set_union(a,b)[o] <==> a[o] || b[o]);
axiom (forall a, b: SetInvoc, y: Invoc :: { Set_union(a, b), a[y] }
  a[y] ==> Set_union(a, b)[y]);
axiom (forall a, b: SetInvoc, y: Invoc :: { Set_union(a, b), b[y] }
  b[y] ==> Set_union(a, b)[y]);
axiom (forall a, b: SetInvoc :: { Set_union(a, b) }
  Set_disjoint(a, b) ==>
    Set_diff(Set_union(a, b), a) == b &&
    Set_diff(Set_union(a, b), b) == a);
// Follows from the general union axiom, but might be still worth including, because disjoint union is a common case:
// axiom (forall a, b: SetInvoc :: { Set_card(Set_union(a, b)) }
//   Set_disjoint(a, b) ==>
//     Set_card(Set_union(a, b)) == Set_card(a) + Set_card(b));

function Set_inter(SetInvoc, SetInvoc): SetInvoc;
axiom (forall a: SetInvoc, b: SetInvoc, o: Invoc :: { Set_inter(a,b)[o] }
  Set_inter(a,b)[o] <==> a[o] && b[o]);

axiom (forall a, b: SetInvoc :: { Set_union(Set_union(a, b), b) }
  Set_union(Set_union(a, b), b) == Set_union(a, b));
axiom (forall a, b: SetInvoc :: { Set_union(a, Set_union(a, b)) }
  Set_union(a, Set_union(a, b)) == Set_union(a, b));
axiom (forall a, b: SetInvoc :: { Set_inter(Set_inter(a, b), b) }
  Set_inter(Set_inter(a, b), b) == Set_inter(a, b));
axiom (forall a, b: SetInvoc :: { Set_inter(a, Set_inter(a, b)) }
  Set_inter(a, Set_inter(a, b)) == Set_inter(a, b));
axiom (forall a, b: SetInvoc :: { Set_card(Set_union(a, b)) }{ Set_card(Set_inter(a, b)) }
  Set_card(Set_union(a, b)) + Set_card(Set_inter(a, b)) == Set_card(a) + Set_card(b));

function Set_diff(SetInvoc, SetInvoc): SetInvoc;
axiom (forall a: SetInvoc, b: SetInvoc, o: Invoc :: { Set_diff(a,b)[o] }
  Set_diff(a,b)[o] <==> a[o] && !b[o]);
axiom (forall a, b: SetInvoc, y: Invoc :: { Set_diff(a, b), b[y] }
  b[y] ==> !Set_diff(a, b)[y] );
axiom (forall a, b: SetInvoc ::
  { Set_card(Set_diff(a, b)) }
  Set_card(Set_diff(a, b)) + Set_card(Set_diff(b, a))
  + Set_card(Set_inter(a, b))
    == Set_card(Set_union(a, b)) &&
  Set_card(Set_diff(a, b)) == Set_card(a) - Set_card(Set_inter(a, b)));

function Set_subset(SetInvoc, SetInvoc): bool;
axiom(forall a: SetInvoc, b: SetInvoc :: { Set_subset(a,b) }
  Set_subset(a,b) <==> (forall o: Invoc :: {a[o]} {b[o]} a[o] ==> b[o]));
// axiom(forall a: SetInvoc, b: SetInvoc ::
//   { Set_subset(a,b), Set_card(a), Set_card(b) }  // very restrictive trigger
//   Set_subset(a,b) ==> Set_card(a) <= Set_card(b));


function Set_equal(SetInvoc, SetInvoc): bool;
axiom(forall a: SetInvoc, b: SetInvoc :: { Set_equal(a,b) }
  Set_equal(a,b) <==> (forall o: Invoc :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom(forall a: SetInvoc, b: SetInvoc :: { Set_equal(a,b) }  // extensionality axiom for sets
  Set_equal(a,b) ==> a == b);

function Set_disjoint(SetInvoc, SetInvoc): bool;
axiom (forall a: SetInvoc, b: SetInvoc :: { Set_disjoint(a,b) }
  Set_disjoint(a,b) <==> (forall o: Invoc :: {a[o]} {b[o]} !a[o] || !b[o]));


// ---------- Types and axiomatization of sequences (of invocations)

// Sequences of invocations
type SeqInvoc;

function Seq_append(s: SeqInvoc, o: Invoc) returns (t: SeqInvoc);

function Seq_elem(n: Invoc, s: SeqInvoc) : bool;

// Relationship between elem and append
axiom (forall n1, n2: Invoc, s: SeqInvoc :: {Seq_elem(n1, Seq_append(s, n2))}
       Seq_elem(n1, Seq_append(s, n2)) <==> Seq_elem(n1, s) || n1 == n2);


// -- New functions and axioms:

function Set_ofSeq(q: SeqInvoc) returns (s: SetInvoc);

// Relation between Set_ofSeq, add, and append
axiom (forall q: SeqInvoc, n: Invoc :: {Set_ofSeq(Seq_append(q, n))}
  Set_ofSeq(Seq_append(q, n)) == Set_add(Set_ofSeq(q), n));

// Relation between Set_ofSeq, Set_elem, and Seq_elem
axiom (forall q: SeqInvoc, n: Invoc :: {Set_ofSeq(q)[n]}
  Seq_elem(n, q) <==> Set_ofSeq(q)[n]);

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
  Seq_distinct(Seq_append(q, n)) && !s[n]
  ==> Seq_restr(Seq_append(q, n), Set_add(s, n)) == Seq_append(Seq_restr(q, s), n));

// Relation between Seq_elem and Seq_restr
axiom (forall q: SeqInvoc, s: SetInvoc, n: Invoc :: {Seq_elem(n, Seq_restr(q, s))}
  Seq_elem(n, Seq_restr(q, s)) <==> Seq_elem(n, q) && s[n]);


// Implicit (strict) order of a sequence
function Seq_ord(q: SeqInvoc, n1, n2: Invoc) : bool;

// This order is transitive
// axiom (forall q: SeqInvoc, n1, n2, n3: Invoc :: //{}
//   Seq_ord(q, n1, n2) && Seq_ord(q, n2, n3) ==> Seq_ord(q, n1, n3));

// Adding to the restriction set is append if ordered correctly
axiom (forall q: SeqInvoc, s: SetInvoc, n: Invoc ::
    {Seq_append(Seq_restr(q, s), n)}
  (forall n1: Invoc :: Seq_elem(n1, Seq_restr(q, s)) ==> Seq_ord(q, n1, n))
  && Seq_elem(n, q) && !s[n]
  ==> Seq_restr(q, Set_add(s, n)) == Seq_append(Seq_restr(q, s), n));

// Appending extends order
axiom (forall q: SeqInvoc, n, n1, n2: Invoc :: {Seq_ord(Seq_append(q, n), n1, n2)}
  Seq_distinct(q) ==>
  (Seq_ord(Seq_append(q, n), n1, n2)
    <==> (Seq_elem(n1, q) && Seq_elem(n2, q) && Seq_ord(q, n1, n2))
      || (Seq_elem(n1, q) && n2 == n)));

