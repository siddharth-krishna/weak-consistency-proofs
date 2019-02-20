# Weak-Consistency Proofs

Provably correct implementations of weakly-consistent data structures.

## Dependencies

* [Boogie]

## Usage

```bash
$ make
```

## Structure

- `lib/`: TODO
- `misc/`: Contains miscellaneous boogie proofs and work-in-progress.
    * `simpleConcurrent/`: Contains java packages to be used for testing with Violat.
    * `build.sh`: Shell commands to be used for Violat testing.
    * `treiber.bpl`: CIVL's proof of Treiber stack, slightly modified.
    * `treiber-known.bpl`: Treiber stack proof, using Grasshopper's reachability axioms and `known()` trigger trick. For some reason this is much slower.
    * `queue-basic.bpl`: CIVL proof of simplified Java/Michael-Scott queue. Uses reachability axioms from `treiber.bpl` and also its version of ownership transfer. Need to add monotonic `size` operation.

[Boogie]: https://github.com/boogie-org/boogie
