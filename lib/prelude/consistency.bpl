/**
 * Imported declarations
 */

// type Invoc;
// type Seq;
// type Set;

/**
 * Exported declarations
 */

 type Vis = [Invoc] Set;

// hb(x, y) : x happens-before y.
// We assume there exists such a function, given by the client program
function hb(x: Invoc, y: Invoc): bool;
axiom (forall n: Invoc :: !hb(n, n));

// A shared global variable that builds the linearization
var {:layer 1,2} lin: Seq;

// A map from invocations to the set of prior invocations visible to them
var {:layer 1,2} vis: Vis;

function {:inline} Consistency.complete(lin: Seq, vis: Vis, this: Invoc): bool {
  vis[this] == Set.ofSeq(lin)
}

function {:inline} Consistency.monotonic(lin: Seq, vis: Vis, this: Invoc): bool {
  (forall i: Invoc :: hb(i, this) ==> Set.subset(vis[i], vis[this]))
}

procedure {:layer 1} Consistency.setVis({:linear "this"} n: Invoc, s: Set)
  modifies vis;
  ensures {:layer 1} vis == old(vis)[n := s];
{
  vis[n] := s;
}

procedure {:layer 1} {:inline 1} Consistency.linPoint({:linear "this"} n: Invoc)
  // To show that linearization is consistent with happens-before
  requires {:layer 1} (forall n1 : Invoc :: hb(n1, n) ==> Seq.elem(n1, lin));
  modifies lin;
{
  lin := Seq.append(lin, n);
}
