# Weak-Consistency Proofs

Provably correct implementations of weakly-consistent data structures.

## Dependencies

* [Boogie]
* [Z3](https://github.com/Z3Prover/z3/). **Important**: need Z3 version 4.5.0, otherwise CIVL blows up!

## Usage

To verify the map implementation:

```bash
$ boogie -noinfer -typeEncoding:m -vcsCores:8 proofs/prelude/*.bpl proofs/adts/map.bpl proofs/impls/array-map.bpl
```

To verify the queue implementation:

```bash
$ boogie -noinfer -typeEncoding:m -vcsCores:8 proofs/prelude/*.bpl proofs/adts/queue.bpl proofs/impls/ms-queue.bpl
```

<!-- ```bash
$ make
``` -->

## Structure

- `proofs/`: The case studies from the paper. Organized as:
    * `prelude/`: Common definitions, axiomatizations of sets, sequences, the heap.
    * `adts/`: The ADT definitions and atomic specification transition systems.
    * `impls/`: The concurrent implementations, and proofs that they are consistent
        with their specification.
- `lib/`: Old version of array-map proof.
- `misc/`: Contains miscellaneous boogie proofs and work-in-progress.
    * `simpleConcurrent/`: Contains java packages to be used for testing with Violat.
    * `build.sh`: Shell commands to be used for Violat testing.
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

[Boogie]: https://github.com/boogie-org/boogie
