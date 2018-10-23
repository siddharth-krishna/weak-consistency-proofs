/**
 * Imported declarations
 */

// type Invoc;
// type SeqInvoc;
// type SetInvoc;

/**
 * Exported declarations
 */

// hb(x, y) : x happens-before y.
// We assume there exists such a function, given by the client program
function hb(x: Invoc, y: Invoc): bool;
axiom (forall n: Invoc :: !hb(n, n));

// A shared global variable that builds the linearization
var {:layer 1,2} lin: SeqInvoc;

// A map from invocations to the set of prior invocations visible to them
var {:layer 1,2} vis: [Invoc] SetInvoc;
