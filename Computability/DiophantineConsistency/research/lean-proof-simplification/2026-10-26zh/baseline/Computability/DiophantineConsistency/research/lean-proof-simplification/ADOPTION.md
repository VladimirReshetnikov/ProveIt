# Adoption record

How each proposal stands against the maintained tree `Computability/DiophantineConsistency/Lean`.
"Adopted" means the change is in the tree and the touched modules passed the
repository-pinned Lean compiler, through `lake build` or explicit
`lake env lean SOURCE -o OBJECT` checks. Validation scope is recorded separately.
Packet names refer to the subdirectories of this directory.

## Adopted or in validation

| Proposal | Packet | Target modules | Status |
|---|---|---|---|
| `patches/pr-congruence.patch` | a | `PRCode`, `ScalarPRCode`, `ScalarPROptimizer` | adopted as supplied; all three rebuilt modules, compiler/client checks and returned-program `rfl` checks pass;34 lines removed |
| `patches/assignment-map.patch` | a | `Representation`, `QuarticCompiler` | adopted; both rebuilt modules and five representative clients/checks pass. The compiler's private wrapper delegates to `natAssignment_comp_map`;26 lines removed including the shared lemma |
| `patches/list-library.patch` (also b `lookup-api`, c `lookup-cleanup`, d, e) | a | `AnnotatedProofChecker`, `AnnotatedRename`, `AnnotatedRuleSide`, `AnnotatedAssumption`, `AnnotatedBound` | adopted with the seven private wrapper signatures retained; five rebuilt modules, four direct clients and five existing focused checks pass;40 lines removed |
| `half_base_bound_31` as a specialisation | f, independently implemented | `SelectiveCoefficientBounds` | adopted using the existing general theorem; module and focused axiom/example checks pass;23 lines removed |
| local mask/carry library cleanups | f, with parallel library-based proofs | `LowMaskCoding`, `MultiTargetCarry` | adopted; both rebuilt modules, both focused checks and five direct clients pass;20 lines removed |
| `finite-residuals.patch` | h | `CompilerSupport`, `DAGQuartic`, `NaturalDAGQuartic`, `QuadraticRegisterSystem` | adopted; four rebuilt modules, two clients, three focused checks and helper/API axiom audit pass;33 lines removed including the shared helper |
| generated circuit Steps (a `generated-steps.patch`, b, f) | a | `SplitCircuitSteps59`, `GapCircuitSteps66` and shared generator | adopted through the maintained generator; both generations and normal/optimized checks pass,14 module rebuilds and12 focused checks pass, all1192 public types preserved and axiom-audited;1646 Lean lines removed including helpers/tables |
| nine-coordinate packaging | f, adapted | `FreeCarrierCoordinates`, `SplitSourceExistence`, `GapSourceExistence66` | adopted as two proof-only transport lemmas; three rebuilt modules, both focused checks, both direct clients and axiom audit pass;26 lines removed including the full39-line helper |
| remaining local proof edits f3–f5 | f, with library-based bounds | `SelectiveCarry`, `NativeCyclicConvolution`, `NativeRadixDigits`, `ArithmeticFiniteSwitch` | adopted with explicit convolution sum reordering; four rebuilt modules, four focused checks, four direct clients and program-constructor/axiom audit pass;22 lines removed |
| `patches/01-pell-factor.patch` | p | HTP `PellRatio90`, `NativeHalfBinomial` | adopted; both rebuilt modules, three direct clients, two existing focused checks and public/helper axiom audits pass;77 net lines removed including the generalized helper and retained wrappers |
| shared signed-root recovery, `patches/main.patch` | m | `NearSquareFinalizer`, `MarginFinalizer` | adopted; both rebuilt modules, three direct clients, three focused checks and old/new axiom audits pass;46 net lines removed including both helpers and wrappers; all nonzero/separation premises retained |
| reuse `nat_zero_or_succ`, `patches/new-simplifications.patch` | l | `ObjectAdditionCancellation`, `ObjectNaturalZero` | adopted; two rebuilt modules, two direct clients, two focused checks and theorem/inferred-instance axiom audit pass;42 lines removed including unused private induction scaffolding, while public formulas and arbitrary internal-omega semantics remain unchanged |
| shared pairing certificate projections, `patches/main.patch` | m | `PairingRepresentation`, `QuadraticNatPairing`, `QuadraticTreeCodeGraphs` | adopted; three rebuilt modules, six direct clients, two focused checks, seven original-constructor `rfl` equalities and old/new axiom audits pass;27 net lines removed including both helper proofs; complete representation data unchanged |
| scanner iteration lemmas (a §4, b, c, d, e) | a | `AnnotatedRenameScan`, `AnnotatedBoundScan`, `AnnotatedLineScan`, `AnnotatedContext` | new axiom-free module `NatIterate`; `scan_zero`, `scan_succ`, `scan_done` are one-line applications; rebuild queued |
| one `axioms_of_zfc_model` (a §7, b) | a | `ObjectArithmetic`, `ObjectMultiplication` and 13 callers | the private copy in `ObjectArithmetic` is made public and the duplicate in `ObjectMultiplication` deleted; rebuild queued |
| `algebra_examples/ArithmeticDAG.patch`, `FirstPellCarrier.patch` | e | `ArithmeticDAG`, `FirstPellCarrier` | applied; rebuild queued |
| `checker_examples/standard_library_cleanup.patch`, `AnnotatedParents` hunk only | e | `AnnotatedParents` | applied (`Option.map_injective`); rebuild queued |

## Pending

| Proposal | Packet | Target | Note |
|---|---|---|---|
| `patches/residual-sum.patch`, e `ShortSystem.patch` | a, e | `ShortSystem` | after the current `ShortSystem` dependents finish building |
| `algebra_examples/Carrier66.patch` | e | `Carrier66` | after the `Carrier66Checks` build finishes |
| `patches/native-coefficient-bounds.patch` (duplicates c `coefficient-refactoring`) | d | `NativeCoefficientBounds` | not integrated: maintained source is still the679-line original; d's complete127-line candidate compiled in the packet, with a local2M-heartbeat budget. A552-line reduction is available; fresh maintained module/client checks and elaboration-cost assessment remain necessary. Do not conflate h's distinct122-line/4M variant or its timings with d |
| parent/tree decoder invariants, `annotated/proposed.patch` | n | `AnnotatedParents`, `AnnotatedProofCode` | uncompiled proposal; claimed54 nonblank declaration lines saved; check actual fuel and raw-input contracts |
| guarded high-color fibers, `wang/proposals/boundary_fibers.patch` | o | `WangTiles942Boundary` | uncompiled proposal; claimed40 lines saved; retain high-color guard, initializer/reset colors and all seam tuples |

## Deferred or not adopted

| Proposal | Packet | Reason |
|---|---|---|
| `patches/conditional-padding.patch` | a | changes a theorem interface in `NativePreliminaryCount2011` / `CurrentCount2011`, which the research session is editing |
| `patches/modulus-reuse.patch` | a | `CurrentEarlyPadding2011` is being edited by the research session |
| `patches/representation-naturality.patch` | d | superseded by a's `assignment-map.patch` |
| `coefficient-refactoring.patch` | c | superseded by d's compiled version |
| `proposals/*.lean`, design-only sections | all | source-only demonstrations; revisit individually |

The PR-congruence proofs use `simp`: both `prec` constructor proofs now depend
on `[propext, Quot.sound]`. The old scalar proof was axiom-free; the old vector
proof used `[propext]`. These are standard axioms. Packet a's
`lean/RecursorCore.lean` gives an axiom-free generic congruence alternative.

The [26 October iteration review](../../reviews/lean-proof-simplification-20261026-root.md)
records the adopted changes above, exact checking scope, authorship and review.
The remaining queued rows retain the separate upstream session's pending
validation status; this merge does not certify those proposed implementations.

The degree certificates of `ShortSystem`, `ShortFrontier` and `ShortReducedStrong` were replaced
independently of these packets, by the `total_degree_bound` tactic in `TotalDegreeBound`.
