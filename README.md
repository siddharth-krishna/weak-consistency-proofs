# Weak-Consistency Proofs

Provably correct implementations of weakly-consistent data structures.
These proofs accompany the paper [Verifying Visibility-Based Weak Consistency](https://arxiv.org/abs/1911.01508) by Siddharth Krishna, Michael Emmi, Constantin Enea, and Dejan Jovanovic.

## Dependencies

* [Boogie](https://github.com/boogie-org/boogie) at commit `7e779369`.
* [Z3](https://github.com/Z3Prover/z3/).
    **Important**: need Z3 version 4.5.0, otherwise CIVL blows up!

## Usage

To verify the map implementation:

```bash
boogie -noinfer -typeEncoding:m -useArrayTheory -vcsCores:8 proofs/prelude/*.bpl proofs/adts/map.bpl proofs/impls/array-map.bpl
```

To verify the queue implementation:

```bash
boogie -noinfer -typeEncoding:m -useArrayTheory -vcsCores:8 proofs/prelude/*.bpl proofs/adts/queue.bpl proofs/impls/ms-queue.bpl
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

## Encoding

We encode the atomic transition system of each ADT specification in CIVL as layer 2 programs in `proofs/adts/`.
These programs contain a call, a return, and a "body" procedure for each method.
The call and return procedures correspond to the call and return AETS actions respectively.
The "body" procedure (for example `get_atomic` of `map.bpl`) corresponds to the atomic block of vis and lin AETS actions.
We also have a `hb_action_atomic` procedure that corresponds to a hb action between two arbitrary invocations.

The state of these layer 2 programs (defined in `proofs/prelude/executions.bpl`) is the abstract execution of the AETS trace, encoded using the following variables:
- `hb`, `lin`, `vis`: these correspond to the respective componenets of the abstract execution.
- Instead of having an `inv` variable, we encode the method name and argument values implicitly using the functions `invoc_m` etc of each `Invoc` element of `lin`.
- We encode the return values of each invocation in the `ret` variable. As our implementations determine the return values at the linearization points, this variable is written to in the "body" procedure for simplicity.

We maintain the invariant that the abstract execution is consistent with the sequential specification by checking that the return value stored in the "body" procedure is consistent with the abstract state as determined by the linearization so far.
For example, `get_atomic` checks that the returned value `v` is equal to `abs[k]` where `abs` is the abstract key-value map determined by `lin`.
