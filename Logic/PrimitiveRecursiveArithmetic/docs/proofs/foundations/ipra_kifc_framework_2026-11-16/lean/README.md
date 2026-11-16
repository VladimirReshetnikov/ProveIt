# KIFC Lean artifacts

The files target the APIs audited at ProveIt commit
`7c1f2594117c15a980d24300593d625722812768`.

## Source-complete kernel adapters

- `KIFC/KernelCore.lean` - proof-producing local rules, implication contracts,
  proof schedules, and the `IPRA.ind` loop-certificate wrapper.
- `KIFC/Examples.lean` - adapters around inherited object-level algebraic
  derivations.
- `KIFC/Checks.lean` - intended axiom audit for the source-complete subset.

These files contain no intentional proof placeholders. They were written
against the inspected API but were not compiled in this artifact environment.

## Interface and generator blueprints

- `KIFC/BooleanBlueprint.lean` - reflected Boolean and bounded-fold contracts.
- `KIFC/SearchBlueprint.lean` - adapter from truth-as-one to the checked
  `IPRADerivations.Core.Search` zero-search engine.
- `KIFC/BoundedExistentialBlueprint.lean` - least-witness/QF-certificate API.
- `KIFC/RelationalBlueprint.lean` - viability and stable-observer interfaces.
- `KIFC/GraphBlueprint.lean` - metalevel node kinds and kernel-facing compiled
  graph object.

These modules expose definitions, structures, and dependency-ordered theorem
targets. They do not postulate generic soundness axioms.

## Placeholder-bearing formalization target

- `KIFC/RetainedTransferBlueprint.lean` - exact theorem decomposition for the
  negative-translation stability, proof translation, retained recovery, and
  final transfer theorem. It contains **18 explicit `sorry` occurrences**.
  They are intentional markers for unfinished Lean implementation and the file
  is not imported by `Checks.lean`.

## Validation boundary

Lean and Lake were unavailable in the artifact environment. No new KIFC
module is claimed to have a clean repository build. Existing ProveIt theorems
are described as inherited checked components only on the basis of the pinned
source and its repository build/axiom-audit records.
