# PA194 formal source-to-physical coverage

`PA194SourceProgram.lean` binds the generated PA194 source tree to the
upstream flattened-tree and instruction semantics and checks the exact
3,673-site count and path-length bound. `PA194CheckCoverage.lean` adapts the
upstream per-instruction coverage proof to the actual unfolded 201-control
parent. Its `checked_at` theorem turns a successful concrete site test into an
exact source instruction and a physical `Implements` proof. All instruction
forms, including both decrement branches and halt, are handled.

`PA194CoverageConditional.lean` proves that if every one of the 3,673
`checkAt` tests succeeds, all source instructions satisfy the `Coverage`
premise of `../pa194-source-iteration`. Consequently, for every valid full
register file and gap, source nonhalting implies nonhalting of the exact
unfolded parent in standard Lean.

The generator emits ordinal batches whose `blockCheck` proofs are kernel
computed, and an aggregator combines the resulting Lean theorems. When all
batches complete, the generated `PA194CoverageComplete` module proves the
unconditional `Coverage` and source-to-parent nonhalting theorems. It does not
use archived source-site or symbolic-outcome records. The pinned Python
translation from the packet's grammar to the formal source tree remains an
explicit source-generation boundary.

Run the full fresh build and all 3,673 site checks sequentially from the
repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-coverage/check.sh
```

Use `--start-site 0 --stop-site 20` for a smaller test; only a complete run
produces the full `Coverage` theorem. All build products are placed in an
isolated temporary `/dev/shm` directory. Theorems here are about standard
finite executions; none is a theorem internal to PA, PRA, or iPRA, and none
alone establishes an equivalence to consistency of PA.

The complete run has passed; `verification.json` records its inputs, result,
and theorem axiom audit. All 368 generated batch objects were retained in a
hash-verified temporary overlay, and the aggregate theorem was independently
recompiled from those objects. The full source-tree generator remains a
pinned Python translation, as described above.
