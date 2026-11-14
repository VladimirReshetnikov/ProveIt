# PA195 dense/native table binding

`PA195DenseBinding.lean` proves `dense_native_halts`: the dense PA195 table
at start 0 with halt 195 halts if and only if its native presentation at
start 74 with halt 254 halts, for every initial head position and complete
binary tape. The proof binds each dense transition to its native transition
using the 196-entry state map, establishes control totality and preservation,
and applies the generic deterministic trace theorem.

`PA195DenseGlobal.lean` composes this result with the seven-fold quotient:
`parent_dense_halts` proves that the unfolded 202-control parent and the
exact dense 195-control PA195 table halt equivalently on any initial tape and
head position. The finite source tables and state map are extracted and checked
against the supplied PA195 archive by `../pa195-quotient/generate.py`.

From the repository root, rebuild the entire proof chain in a private temporary
`/dev/shm` directory and check the final theorem:

```sh
Computability/BusyBeaver/Research/PA/pa195-dense/check.sh
```

These are standard-Lean finite-trace statements. They do not yet identify the
full-tape model with `PA195.Literal`'s zipper semantics, prove the connection
to PA consistency, or establish a theorem inside PRA or iPRA.
