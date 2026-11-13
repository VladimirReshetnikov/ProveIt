# Fixed85 lexical tactic hazard triage and isolated alternatives

This packet contains **unelaborated, inert source alternatives**. It does not
change any pinned historical source, select any provider, stage files, run
Lean, or establish an iPRA proof. The fixed85 lexical source inventory is a
bounded starting point, not a verified Lean import closure.

Among its 94 external/frontier names beginning with `Mathlib.`, the observed
local mathlib source tree has every corresponding source except
`Mathlib.Tactic.Omega`, imported by the separately addressed
`ResidueSignFreePower`. This check does not resolve Foundation, BusyBeaver,
other package roots, compiled objects or search-path collisions.

The same lexical inventory reaches eight **additional research modules**
with `omega` calls in proofs quantified over abstract model type V. Such
calls are hazards for elaboration, not a demonstrated kernel failure. The
following alternatives preserve each original logical namespace and theorem
signatures, but have different current basenames so they cannot silently
replace the pinned providers:

| Priority | Logical module | Abstract-V calls | Direct replacement pattern |
| --- | --- | --- | --- |
| 1 | `ResidueRankLower` | 5 | Add/cancel inequalities, successor bounds, and explicit multiplication. |
| 1 | `ResidueExactIndexWitness` | 1 | Derive q≥3 from the two positive factors and the gap. |
| 1 | `ResidueExactIndexModel` | 1 | The same q≥3 argument for the sibling interface. |
| 2 | `Residue90FyForce` | 1 | Add two separate positive-unit bounds. |
| 2 | `AQ17Forced105Arithmetic` | 2 | Contradict strict increase and the explicit 4≤1 inequality. |
| 3 | `Residue90FirstNormGap` | 1 | Add the two shifted-coordinate lower bounds. |
| 3 | `Residue90CompactGraphGamma` | 1 | Add one to the positive b lower bound. |
| 3 | `Residue90GammaModel` | 1 | Monotonic addition gives R+1≤R+q³+q+1. |

The priority ordering is a review queue, informed by shortest lexical distance
to the fixed85 root; it is not an estimate of actual failure likelihood or a
runnable build order. The receipt also records direct consumers and the
reverse-reachable local-module count for every candidate. The prior isolated
`ResidueSignFreePower` replacement is separate and must also be selected if a
future build chooses this approach.

The inventory found 143 other repository-local modules with lexical `omega`
hits. The simple scanner does not reliably distinguish comments, quoted
examples, ordinary `ℕ`/`ℤ` uses, or abstract-model goals; many inspected
`ArithmeticAdaptive*` hits concern standard natural-number bounds. They are
not declared defects, and this packet does not claim to have audited all of
them. The `Positive84OrientedPower` lexical hit is a comment, not a tactic.
Other unsupported imports, source-level errors and proof escapes may remain.

For a future isolated overlay, each desired alternative would need selection
as the **sole provider under its original logical module name**, then its
transitive reverse consumers and any affected dependencies must be rebuilt
against authenticated providers. Merely adding these uniquely named files to
a search path does not perform that override. Existing objects, evidence and
source snapshots must remain protected, and no disk reservation follows from
this source inventory. Never load an old and new same-namespace provider
in the same environment.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-fixed85-omega-hazards-draft/check.py
```

The check verifies pinned inputs and read-only regeneration of alternatives,
compares theorem headers and namespaces, inventories the bounded import graph,
and tests finite arithmetic controls. It does not execute Lean, prove the new
scripts, authenticate providers, or validate the endpoint/PDF.
