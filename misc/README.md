This directory contains miscellaneous boogie proofs and works-in-progress.

* `simpleConcurrent/`: Contains java packages to be used for testing with Violat.
* `build.sh`: Shell commands to be used for Violat testing.
* `hash-map.bpl`: This is the same implementation as in `../proofs/` but with
    inlined prelude and adt definitions.
* `array-map.bpl`: This is a simpler version of `hash-map.bpl` where the hash
    function is identity.
* `queue.bpl`: This is the same implementation as in `../proofs/` but with
    inlined prelude and adt definitions.
* `treiber.bpl`: CIVL's proof of Treiber stack, slightly modified.
* `treiber-known.bpl`: Treiber stack proof, using Grasshopper's reachability axioms
    and `known()` trigger trick.
* `queue-basic.bpl`: CIVL proof of simplified Java/Michael-Scott queue.
    Uses reachability axioms from `treiber.bpl` and also its version of ownership
    transfer. Need to add monotonic `size` operation.
* `queue-basic-known.bpl`: CIVL proof of simplified Java/Michael-Scott queue.
    Uses Grasshopper's reachability axioms.
    Has `push`, `pop`, and `size`, and proves memory safety.
    Needs invariant tying abstract state to concrete state to prove monotonicity.