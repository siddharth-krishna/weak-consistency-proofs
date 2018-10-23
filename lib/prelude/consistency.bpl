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
