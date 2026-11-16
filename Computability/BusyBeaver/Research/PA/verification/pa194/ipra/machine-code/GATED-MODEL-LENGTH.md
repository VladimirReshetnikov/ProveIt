# Conditional no-prior-halt simulation and witness extraction

`PA194GatedModelLength.lean` proves three **conditional Lean theorems about
every candidate-PRA model whose arithmetic reduct satisfies IΣ₁**. The source
state, its transition, physical frame, elapsed clock, per-step cost, active
prefix, validity, normal-instruction, source-hit and physical-halt predicates
are all abstract. The quantified n, t and witnesses may be nonstandard model
elements. The theorems are not object-theory iPRA derivations.

`simulateBeforeHalt` proves for every model n that an active prefix implies
`good(state n)`, physical `stepper(elapsed n,start) = frame(state n)`, and
`n ≤ elapsed n`. It explicitly assumes:

* This implication is a Σ₁-definable predicate of n, and its active-zero base
  case holds, including the initial clock lower bound.
* An active prefix at `n+1` implies the prefix at n was active and state n's
  source instruction was normal.
* The modeled state and clock have their stated successor recurrences.
* Every good normal state remains good after the source transition, its
  physical segment reaches the next frame at the stated cost, and the cost is
  at least one.

The proof uses model IΣ₁ induction and literal-stepper clock composition. It
never requires a ready-to-halt frame to execute a normal transition or to
remain a nonhalting frame after that halt instruction.

`haltToSourceHit` assumes the gated synchronization above, physical halt
persistence at later clock values, nonhalting of every good frame, and an
explicit bounded first-hit supplier: failure of the active prefix at `t+1`
yields an index `i ≤ t` with a source hit. Under those hypotheses, literal
halt at t yields a source-hit witness at some i ≤ t. The first-hit supplier is
**assumed**, not constructed from a particular code in this file.

`sourceHitToHalt` independently assumes the gated synchronization, an active
first-hit supplier (a source hit at n supplies an active source hit at i ≤ n),
and a physical halt-instruction segment contract for each good hit state. It
then yields a literal halt at the explicit sum of the prefix and halt-segment
clocks. It does not need or use the other direction's halt persistence or
nonhalting-frame premises.

Neither set of premises has been discharged for the complete PA194 source
program. In particular this package does not implement the active-prefix or
bounded-first-hit code, verify all source-site segments and exact clocks, prove
halt persistence for the relevant predicate, or connect source hits to PA
refutations. It therefore proves neither PA194/Con(PA) implication. The three
Lean axiom audits list `propext`, `Classical.choice`, and `Quot.sound`, without
`sorryAx`; these are Lean metatheoretic assumptions, not new object axioms.

## Staged replay

`check-gated-model-length.sh` recompiles the conditional composition and gated
framework source modules in one fresh output, checks their hashes and axiom
reports, and refuses `sorryAx`. It uses the separately built coherent PA194
machine root and prebuilt project/foundation/Lake roots. That coherent build's
startup/header baseline and general logic objects remain separately staged
prerequisites; checking its manifest and direct objects does not itself
rebuild or authenticate their transitive closure. All example paths are
session-local.

From the repository root:

```sh
base=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
bash "$base/check-gated-model-length.sh" \
  "$PWD" "$base" \
  /dev/shm/pa194-unified-coherent/build \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The checker rejects inherited Git-internal overrides and does not set them.
