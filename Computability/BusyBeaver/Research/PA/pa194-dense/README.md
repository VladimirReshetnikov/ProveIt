# PA194 dense/native table binding

`PA194DenseBinding.lean` proves that the dense PA194 machine at start 0 and
halt 194 halts if and only if its native 74/254 presentation halts, for every
initial head position and complete binary tape. `PA194DenseGlobal.lean`
composes this with the seven-fold quotient: `parent_dense_halts` proves that
the exact unfolded 201-control parent and delivered dense 194-control PA194
table have equivalent standard finite-run halting behavior on every tape.

Rebuild all Lean dependencies in a temporary `/dev/shm` directory and check
the theorem from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-dense/check.sh
```

The tables and state map come from the hash-pinned packet via
`../pa194-quotient/generate.py`. This result does not yet identify the
full-tape model with the PA194 zipper semantics, connect source nonhalting to
PA consistency, or establish a theorem internal to PRA or iPRA.
