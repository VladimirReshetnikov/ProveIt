# Semantic review: perform collection transport once

Baseline: `6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95` of
`VladimirReshetnikov/ProveIt`.

## Main recommendation

Move the existing proof that the bisimulation quotient has *full, native-equality,
formula-indexed GIC* before its Separation and Replacement developments. Derive those
two schemas inside the quotient by ordinary equality reasoning. This is a proof-order
change that removes separate quotient lifting and bisimulation-invariance arguments
for every schema. It composes with the existing `quotient-unification` proposal,
which has a different purpose: eliminate the duplicate CP/GIC and QHyp quotient
implementations.

The mathematical GIC implications are standard and already discussed in this
repository's `mira_containers.md`. The new contribution here is the concrete,
kernel-checked use of those implications to reorganize the current K215 proof
closure. Do not claim a new set-theoretic result.

## Exact source observation

All source paths below have prefix
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`.

* `KQ1Collect.lean` imports `KQ1Power`, but its proofs do not use any theorem about
  power sets or separation. They need `KQ1Model`, the profile interfaces already
  imported by that module, and `KQ1Separation.liftEnv`/`mk_liftEnv`.
* `KQ1Collect.quotient_collection` already transports every actual `Form` matrix.
  It uses `translated_instance`, the equality-free translation, and one
  two-argument invariance proof. `quotient_fullGIC` therefore has no
  `EqualityFree phi` premise.
* `KQ1Separation.quotient_separation` nevertheless separately selects a lifted
  environment, invokes interpreted separation, performs quotient inductions,
  and transports satisfaction again.
* `KQ1Replacement.quotient_replacement` similarly translates functionality to
  bisimilarity, invokes interpreted replacement, and performs quotient witness
  reconstruction. Its private route includes `quotient_relOf`.
* `KQ1Power.trace_instance` uses the weaker
  `KQ1Separation.separation_instance : ModelsGIC mem -> ...` at the single
  matrix `.fMem 0 1`. Preserve this route. In particular the existing CP/GIC to
  QHyp adapter needs raw trace support to establish `QHyp.power`.

## The small theorem which changes the architecture

Write `E(x,a)` for membership and `R(x,y)` for a partial functional relation
on `a`. Assume one collection instance for the guarded relation
`E(x,a) /\ R(x,y)`. Then there is `b` such that

```
E(y,b) <-> exists x, E(x,a) /\ R(x,y).
```

Global support supplies the forward implication. For the reverse implication,
collection selects an output `z` in `b` for input `x`; partial functionality
gives `z = y`. This proof is constructive and uses no choice or extensionality.

The guard is essential: the repository's collection support only states that
each collected output has *some* input, not necessarily an input in `a`.
Partial identity, `R(x,y) := x = y /\ P(x)`, yields Separation.

All actual schema applications remain first order. The new `imageMatrix` is
`Mem(0,2) /\ rename(imageRename, phi)` with argument map
`0 -> 1`, `1 -> 0`, `k+2 -> k+3`. The `filterMatrix` is
`Eq(0,1) /\ rename(succ, phi)`. Their satisfaction lemmas are checked against
the real repository `Form`, `Sat`, `relOf`, and environment conventions.
There is no hypothesis asserting collection for every semantic predicate.

## Checked artifacts

* `CollectionFirst.lean`: 62 physical lines, 2,372 bytes. Standalone `Std`
  version matching the repository definitions. Both central theorems have
  no axioms.
* `GICConsequences.lean`: 110 lines, 4,279 bytes. Uses actual repository
  definitions. `exact_image_of_collection` has no axioms. `replacement` and
  `separation` report `[propext]` (from the existing renaming infrastructure).
  `separation_of_replacement` isolates the reusable partial-identity argument.
* `QuotientCollectionFirst.lean`: 109 lines, 4,702 bytes. The existing
  `KQ1Collect` argument under a new namespace, with `liftEnv` moved before it.
  Its only direct import is `KQ1Model`, proving there is no need to import
  Separation or Power before quotient collection.
* `QuotientConsequenceAdapters.lean`: 39 lines, 1,588 bytes. Reproduces the
  exact public types of `quotient_separation` and `quotient_replacement`,
  under a fresh namespace. Each proof is one application of the generic
  native theorem to `quotient_fullGIC`.
* `WFSeparationAdapter.lean`: 29 lines, 1,007 bytes. The exact current
  `WFModel.domain_separation` statement, derived from `domain_replacement`
  using the generic partial-identity theorem. Its reported axioms are
  `[propext, Quot.sound]`.
* `check_repository.py`: compiles the 35-module local import closure serially.
  `repository-check.log` records all successful exit codes and axiom reports.

Compiler: Lean 4.32.0. All 35 modules pass. The two quotient adapter theorems
report exactly `[propext, Classical.choice, Quot.sound]`. No new axiom,
`sorry`, `admit`, native decision oracle, or mathematical model-existence
assumption is introduced. The dependency modules produce their existing
unused-variable linter warnings; the newly authored modules do not.

This verifies the actual source-level schema route. It does **not** rebuild
`KEndpoint215`, the binary machine certificate, or the complete repository.
Production sources are untouched.

## Integration order

1. Introduce the generic native theorem module at the `ProfileSyntax`/ZF
   interface. The prototype currently imports `ProfileModel` for its
   `collectionInstance_congr`; its import can be further narrowed by moving
   that generic helper only if the change gives a concrete benefit.
2. Move quotient-environment representatives to `KQ1Model` or a small
   `KQ1Environment` module. Retain aliases for public old names if needed.
3. Let `KQ1Collect` import only the quotient model/environment layer.
4. Replace the public Separation and Replacement proof bodies by the
   checked adapters. Keep the existing schema-form wrappers.
5. Retain the weak raw trace instance needed by `KQ1Power` and
   `QuotientModel.ofCPGIC`, preferably in a small raw-trace module. This avoids
   accidentally requiring QHyp to prove its own power field.
6. Remove unused raw interpreted-separation and interpreted-replacement
   helpers only after a reverse-use scan. Public names cited by clients can
   stay as compatibility wrappers where their statements are recovered;
   `SubD` in the old interpreted-separation theorem is an extra property and
   must not be silently claimed from quotient Separation.
7. In `WFModelCore`, move `domain_separation` below `domain_replacement` and
   replace its body by the checked second adapter. The Replacement proof
   never calls the old Separation theorem. Keep ambient `H.sep` uses where
   they are still needed elsewhere in the well-founded-part construction.
8. Rebuild `KQ1ZF`, `KLowerQHyp`, `KEndpoint`, `KEndpoint215`, all CP/GIC
   clients, and assumption reports before production adoption.

## Honest size accounting

Current files contain 118 lines (`KQ1Separation`), 143
(`KQ1Replacement`), and 92 (`KQ1Collect`), totaling 353 physical lines.
The two public theorem bodies alone contain 14 + 25 = 39 lines and become
2 + 2 = 4 lines, a verified local body reduction of 35 lines. This is **not**
a net repository saving: the generic consequence module adds 110 lines,
and environment movement/weak raw trace compatibility must be accounted for.
Conversely, now-unused raw replacement translation, equivariance and
quotient-lifting helpers become removable. A production deletion total
requires the actual adoption patch and its compatibility policy. The checked
WF adapter similarly turns a 14-line body into a 2-line application.

A conservative design budget, if unused internal helpers are retired, is:
71 old raw-Replacement-helper lines plus 16 interpreted-Separation lines
plus 35 public-body lines removed, 110 new generic-module lines added,
and 12 more body lines removed by the WF use. That is 24 lines before
import and compatibility overhead, with environment movement neutral.
This budget is an explicitly uncommitted design estimate, not an applied
production diff. Audit prints and generic schema-form convenience wrappers
can live outside the production core, but that should be measured in the
eventual patch rather than counted now.

The primary benefit is fewer independent proof obligations: one quotient
collection transport replaces separate transports for Collection,
Separation, and Replacement. No claim about kernel time or proof-term size
is made without benchmarking an adopted patch.

The partial-Replacement observation must not be applied mechanically to
`ConstructibleZF.inL_sep`: `inL_repl` calls `inL_sep` to construct its image,
so deleting that Separation proof in favor of `inL_repl` would be circular.

## Sources and prior-art distinction

Use fixed-commit links, for example:

`https://github.com/VladimirReshetnikov/ProveIt/blob/6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Collect.lean`

Relevant baseline modules: `KQHyp`, `KQ1Model`, `KQ1Collect`,
`KQ1Separation`, `KQ1Replacement`, `KQ1Power`, `ProfileCollection`,
`ProfileSyntax`, and `ZF.Zf`/`FirstOrder.Fol`.
The separate unification proposal is at
`Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/quotient-unification/README.md`.
That packet already claims +147/-748 lines and a 25-module serial check;
do not count those savings as a new result of this proposal.
