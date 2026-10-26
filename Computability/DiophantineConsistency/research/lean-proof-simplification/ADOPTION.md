# Adoption record

How each proposal stands against the maintained tree `Computability/DiophantineConsistency/Lean`.
"Adopted" means the change is in the tree and the touched modules were rebuilt with `lake build`.
Packet names refer to the subdirectories of this directory.

## Adopted or in validation

| Proposal | Packet | Target modules | Status |
|---|---|---|---|
| `patches/pr-congruence.patch` | a | `PRCode`, `ScalarPRCode`, `ScalarPROptimizer` | applied as supplied; rebuild queued |
| `patches/assignment-map.patch` | a | `Representation` | applied as supplied (adds `natAssignment_comp_map`); rebuild queued. `QuarticCompiler` now uses the same lemma in place of its private `assignment_comp` |
| `patches/list-library.patch` (also b `lookup-api`, c `lookup-cleanup`, d, e) | a | `AnnotatedProofChecker`, `AnnotatedRename`, `AnnotatedRuleSide`, `AnnotatedAssumption`, `AnnotatedBound` | applied, then taken one step further: the private wrappers are deleted and call sites use `List.mem_of_getElem?` / `List.getElem?_of_mem`; rebuild queued |
| scanner iteration lemmas (a §4, b, c, d, e) | a | `AnnotatedRenameScan`, `AnnotatedBoundScan`, `AnnotatedLineScan`, `AnnotatedContext` | new axiom-free module `NatIterate`; `scan_zero`, `scan_succ`, `scan_done` are one-line applications; rebuild queued |
| one `axioms_of_zfc_model` (a §7, b) | a | `ObjectArithmetic`, `ObjectMultiplication` and 13 callers | the private copy in `ObjectArithmetic` is made public and the duplicate in `ObjectMultiplication` deleted; rebuild queued |
| `patches/native-coefficient-bounds.patch` (duplicates c `coefficient-refactoring`) | d | `NativeCoefficientBounds` | applied (the packet compiled the full module); rebuild queued |
| `algebra_examples/ArithmeticDAG.patch`, `FirstPellCarrier.patch` | e | `ArithmeticDAG`, `FirstPellCarrier` | applied; rebuild queued |
| `checker_examples/standard_library_cleanup.patch`, `AnnotatedParents` hunk only | e | `AnnotatedParents` | applied (`Option.map_injective`); rebuild queued |

## Pending

| Proposal | Packet | Target | Note |
|---|---|---|---|
| `patches/residual-sum.patch`, e `ShortSystem.patch` | a, e | `ShortSystem` | after the current `ShortSystem` dependents finish building |
| `algebra_examples/Carrier66.patch` | e | `Carrier66` | after the `Carrier66Checks` build finishes |
| generated circuit Steps (a `generated-steps.patch`, b, f) | a | `SplitCircuitSteps59`, `GapCircuitSteps66` | needs the generators in `tools/` updated with it |
| `half_base_bound_31` as a specialisation | f | `SelectiveCoefficientBounds` | |
| local proof edits f3–f5 | f | `LowMaskCoding`, `MultiTargetCarry`, `SelectiveCarry`, `NativeCyclicConvolution`, `NativeRadixDigits`, `ArithmeticFiniteSwitch` | |
| nine-coordinate packaging | f | `SplitSourceExistence`, `GapSourceExistence66` | 60 byte-identical lines |

## Deferred or not adopted

| Proposal | Packet | Reason |
|---|---|---|
| `patches/conditional-padding.patch` | a | changes a theorem interface in `NativePreliminaryCount2011` / `CurrentCount2011`, which the research session is editing |
| `patches/modulus-reuse.patch` | a | `CurrentEarlyPadding2011` is being edited by the research session |
| `patches/representation-naturality.patch` | d | superseded by a's `assignment-map.patch` |
| `coefficient-refactoring.patch` | c | superseded by d's compiled version |
| `proposals/*.lean`, design-only sections | all | source-only demonstrations; revisit individually |

The PR-congruence proofs use `simp`, so the formerly axiom-free `prec` constructors of `PRCode` and
`ScalarPRCode` now depend on `propext` (and `Quot.sound` for the vector form). These are standard
axioms; packet a's `lean/RecursorCore.lean` gives an axiom-free alternative if that ever matters.

The degree certificates of `ShortSystem`, `ShortFrontier` and `ShortReducedStrong` were replaced
independently of these packets, by the `total_degree_bound` tactic in `TotalDegreeBound`.
