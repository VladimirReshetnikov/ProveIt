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
| `patches/list-library.patch` (also b `lookup-api`, c `lookup-cleanup`, d, e) | a | `AnnotatedProofChecker`, `AnnotatedRename`, `AnnotatedRuleSide`, `AnnotatedAssumption`, `AnnotatedBound` | adopted with the seven private wrapper signatures retained; five rebuilt modules, four direct clients and five existing focused checks pass;40 lines removed. The one-line wrappers were then deleted and their call sites call `List.mem_of_getElem?` / `List.getElem?_of_mem` directly; the five modules and their annotated clients rebuilt with `lake build` |
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
| `patches/native-coefficient-bounds.patch` (duplicates c `coefficient-refactoring`) | d | `NativeCoefficientBounds` | adopted as the complete127-line candidate; named module build, existing focused check, both native source/equation clients and all eight public axiom comparisons pass;552 lines removed. Local2M-heartbeat proof took160.69s and2139032KiB RSS; compiled object grew from1372672 to3686520 bytes. This is a source-maintenance tradeoff, not a speedup |
| parent/tree decoder invariants, `annotated/proposed.patch` | n | `AnnotatedParents`, `AnnotatedProofCode` | adopted; five fresh builds, five existing focused checks and two axiom audits pass, with26 true controls;53 physical lines removed including `decode_spec`. Raw input/fuel and executable definitions are unchanged; `decoded_depth_le` now also uses standard `Classical.choice`, while checker-soundness axiom sets are unchanged |
| `algebra_examples/ArithmeticDAG.patch`, `FirstPellCarrier.patch`, `Carrier66.patch` | e | `ArithmeticDAG`, `FirstPellCarrier`, `Carrier66` | adopted as proof-body changes; six builds including three missing prerequisites, three direct clients, five focused checks and final axiom audit pass;31 lines removed; evaluator data and all positivity/rank premises unchanged |
| `checker_examples/standard_library_cleanup.patch`, `AnnotatedParents` hunk only | e | `AnnotatedParents` | adopted after the separate decoder refactor; module/client builds, existing focused check and baseline/final axiom comparison pass; two further lines removed by `Option.map_injective` |
| scanner iteration lemmas (a §4, b, c, d, e) | a, adapted | `NatIterate`, `AnnotatedRenameScan`, `AnnotatedBoundScan`, `AnnotatedLineScan`, `AnnotatedContext` | adopted as `dbc6446fa7`;11 source/client builds,10 focused checks,20-old-result axiom comparison and two-helper audit pass (23 final calls,49 true controls);23 net lines removed including the full19-line axiom-free helper. An initial motive-inference failure was corrected with an explicit annotation; independent full review passes |
| shared ZFC-model extraction (a §7, b) | a, adapted | `ObjectArithmetic`, `ObjectMultiplication` | adopted as `3814a1da29`; lower public `zfAxioms_of_zfc_model` retains the six-axiom proof, and the old multiplication API is a wrapper; all13 callers unchanged. Ten final module/client/check/API-audit calls pass after the baseline audit; five old axiom reports are byte-identical;12 lines removed |
| `algebra_examples/ShortSystem.patch`, `minima/01-negative-norm-reuse.patch` | e, q (also a `residual-sum`) | `ShortSystem`, `MinimumNorm` | adopted as `f1b8c4abc3`; unchanged `TotalDegreeBound` prerequisite, both modules, `Carrier65` / `ShortFrontier` / `ShortReducedStrong` clients, `ShortEquationAxioms` / `ProposalAxioms` checks and49-public-result axiom comparison pass (nine final calls);40 lines removed, signatures/data unchanged; independent full review passes |
| isolated quadratic coefficient calculation | t | `QuadraticFiber`, `QuadraticCoding`, `MultiQuadraticCoding`, `SelectiveQuadraticCoding` | adopted as `fad90f705b`; four builds, five clients (`DegreeSeparatedCoding`, `SelectiveCertificate46`, `SelectiveCertificate52`, `SelectiveCarry`, `MultiTargetCarry`), three checks,24-old-result axiom comparison and standard-three helper audit pass (14 final calls);20 net lines removed including the full32-line helper; independent full review passes |
| `patches/specifications.patch` | s | `ObjectAdditionLaws`, `ObjectAdditionCancellation`, `ObjectMultiplicationLaws`, `ObjectDistributivity`, `ObjectNaturalOrder`, `ObjectNaturalExpression`, `ObjectCodeBound`, `ObjectCodeSeal` | adopted as `4ae1ff991a`; eight module builds, three representative clients, six existing focused checks and107-public-result axiom comparison pass (18 final calls); all old axiom reports byte-identical,133 lines removed with no helper overhead. Formula/data/binder layouts and arbitrary internal-model premises unchanged; independent full review passes |
| formal two-radicand identity, `patches/refined-pair-algebraic.patch` | w | `RefinedPair` | adopted as `57a5eed4d8`; target, three clients, 63-endpoint `CompilerAxioms` check, two-old-result comparison and new-core audit pass (seven final calls after the earlier baseline). Source grows from 83 to 86 lines: a formal polynomial identity replaces chosen complex roots and simplifies mathematical prerequisites. The direct complex import is removed, though Complex remains transitively available; independent full review passes |
| lower-ratio reuse, `patches/pell.patch`, native-power hunk only | s | `NativePellPower` | adopted as `f1949d7be7`; target, three clients, four focused checks and nine-old-result axiom comparison pass (nine final calls after baseline); 17 net lines removed after charging the added lower HTP import. The doubled coordinate, factor two and all nine public signatures remain unchanged; an existing unused-`hd` client warning remains; independent full review passes |
| `native-proofs/pell-oddness-only.patch` | k | `NativePellStepDown` | adopted as `f3b6ad87d0`; unchanged prerequisite, target, three clients, four focused checks and seven-old-result axiom comparison pass (ten final calls); 20 net lines removed after charging the added import. Initial target invocation stopped before elaboration because the `SignedPellResidue` object was absent; the unchanged prerequisite and target retry passed. An old-cache premature audit is excluded. All premises and sign cases remain unchanged; retained `hy` now has an unused-variable warning; independent full review passes |
| inverse-pairing certificate reuse | k, adapted using the already adopted m helpers | `RegisterNatPairing` | adopted as `4fc484d4c8`; target, existing `RegisterRelations` client/focus, 13-old-result comparison and whole-old-source equality audit pass (four final calls after baseline); 12 lines removed without helpers or imports. Complete relation/graph records and the all-input program are equal by `rfl`; witness slots and all public signatures are unchanged. Independent full review passes; the reviewer suggested this reuse during the census but did not author the implementation |
| `patches/NativeCyclicRotation.patch` | i | `NativeCyclicRotation` | adopted as `afbec38df7`; 17 lines removed by specializing existing convolution to a single impulse, with no helper or import. In the joint rotation/degree batch, both targets, five source/client builds including the planned unchanged `NativeCyclicCarry` prerequisite, four focused checks and 22-old-result comparison pass (12 final calls after baseline). Radix-one and length-one cases and all definitions/premises remain unchanged; independent full review passes |
| `patches/SelectiveCarry.patch`, adapted to reuse the degree theorem | i | `SelectiveCarry` | adopted as `8274c8f6b2`; 18 net lines removed after charging the added polynomial big-operators import, with no helper. Existing degree/coefficient lemmas are reordered so coefficient vanishing follows from the shared degree bound. The joint 12-call validation above passes; polynomial data, truncated exponents and all public statements remain unchanged, including empty/zero cases; independent full review passes |
| last-row native span bound | y | `NativeQuadraticPositions` | adopted as `39a52d6353`; rows 0–20 use the general subtraction bound, leaving only five actual supported entries of row 21. Target, both direct clients, three focused checks and 15-old-result axiom comparison pass (seven final calls after baseline); 81 lines removed with no helper/import/data change. Independent complete-source review passes |
| `patches/01-jones-evaluation-api.patch` | ze | `JonesSyntax`, `ExecutableJones` | adopted as `80eabc57c8`; five existing semantic bridges become public and replace five duplicated private proofs. Both targets, four direct clients, 63-endpoint compiler check, 26-old-result comparison and five-bridge audit pass (nine final calls after baseline); 49 net lines removed, all executable definitions unchanged. Independent complete-source review passes |
| `patches/syntax-coefficients.patch` | zg | `SyntaxCoefficients` | adopted as `ed32381986`; one private interpretation-as-list-sum bridge replaces repeated algebraic inductions. Charging the helper and added import, 10 net lines removed. Joint nine-call validation with the object port passes: two targets, three direct clients, three existing focused checks and 15-old-result axiom comparison. Sparse syntax/coefficient data and all old public statements unchanged; independent complete-source review passes |
| `patches/environment-restriction.patch`, with explicit predicate and direct equation semantics | zg, adapted | `ObjectPolynomial` | adopted as `be154fa93b`; injective coordinate restriction and the existing empty-set default cover every internal tuple, including zero variables and nonstandard naturals. The initial unannotated candidate failed motive inference; adding the explicit predicate fixed it. All nine joint final calls above pass, old axiom reports are identical, and formula/binder data are unchanged. 16 net lines removed; independent complete-source review passes |
| signed-square disequality, `patches/semantic_arithmetic_nonzero.patch` | zj | `ArithmeticNonzero` | adopted as `91bb6ff650`; integer square positivity/discreteness replaces sign cases. Target, both direct clients, existing `ProposalAxioms`, four-old-declaration comparison and complete original-record `rfl` audit pass (six final calls after baseline); 3 lines removed. Witness/expression data unchanged; independent full review passes |
| `patches/finite-order-rigidity.patch` | zj | `WangTiles942PhysicalOrder` | adopted as `52519f1cd6`; finite order-hom identity replaces the custom induction, retaining empty/singleton cases. Target, existing focused module, 23-old-result comparison and direct residue client pass; the client run is shared with the common-modulus port. Including the import, 25 lines removed, all physical data unchanged; independent full review passes |
| `power/patches/guarded_power_cast_fusion.patch` | zl | `PrimePowerOrder` | adopted as `8772c3b3a9`; one guarded cast/subtraction rewrite replaces both iff directions, preserving zero modulus/exponent. 7 lines removed, with no helper/import. Joint nine-call power validation passes: two targets, two direct clients, four existing focused modules and 19-old-result comparison. All old reports identical; independent full review passes |
| `power/patches/exact_order_clients.patch`, repaired dependent transport | zl, adapted | `CurrentPowerCoordinates2011` | adopted as `bd12ef208c`; exact-order endpoint reuse and direct modulus rewriting remove the one-use transport helper. The uncompiled supplied candidate failed three dependent-`ZMod` `simpa` proofs; explicit `rw` steps repair them, charging five extra lines. Final saving 9 lines, not the proposed 14. The joint nine final calls above pass, with all old types/data and opaque-base protection unchanged. Independent review passes for the actual repaired source |
| `patches/01-common-modulus.patch` | zn | `CurrentKernelResidues2011` | adopted as `1eb5d15000`; 177 numeric chunk certificates become 59 modulo a common multiple, then project to the old factors. Target, direct units client, both existing focused modules, 15-old-declaration comparison and new common-residue audit pass (six final calls); old reports identical, new API standard-three axioms. All definitions and physical/reindex/raw-word bridge remain exact. 417 lines removed including the new API/helper; independent full review passes; no speedup claim |
| f T03 (`hpow` by `Nat.sub_add_cancel`) | f | `SelectiveCoefficientBounds.half_base_bound` | adopted; module rebuilt with `lake build` |
| generator I/O | — | `tools/generate_split_recipe_steps59.py`, `tools/generate_gap_recipe_steps66.py` | both read and write UTF-8 with LF, so `--check` and regeneration behave the same on Windows; both `--check` runs pass |
| `patches/formula-minimum.patch` | x | `AnnotatedClosure` | adopted as `9c37c0868c`; pairing/fork monotonicity gives the uniform44 formula-code bound from the outer constructor, replacing structural induction. Including all five private supporting lemmas,19 lines removed. Joint closure/binary validation passes11 final calls: two targets, three clients, five focuses and23-old-declaration comparison; all reports identical,14 runtime controls true. All program data remain literal; independent full review passes |
| `patches/width-divisibility.patch` | zg | `NativeBinaryScale` | adopted as `7f35ee6786`; the natural power-remainder identity and power-at-most-one criterion replace a separate equality/injectivity argument.4 lines removed without helpers/imports; old positive-width API retained. The joint11-call suite above passes; existing unused-`hd` warning remains. Binary/scale clients also validate the Pell port below; independent full review passes |
| `patches/logic-proof-refinements.patch`, without redundant import | incoming proof deltas | `ObjectDivision`, `ObjectZeroTest` | adopted as `5bb366fcb8`; internal semiring cancellation replaces repeated gap reconstruction and a Boolean case split.7 lines removed, all formulas/definitions/types/imports unchanged. Eight final calls pass: two targets, two clients, three focuses and23-old-declaration comparison. Stale imported anonymous-instance names required14 unchanged cache refreshes and both original sources rebuilt before the coherent baseline; initial target/diagnostic failures preserved. Independent full review passes |
| `lte/prime-power-spectrum.patch`, composed over the existing guarded cast bridge | zo, adapted | `PrimePowerOrder` | adopted as `25feb7f728`; arbitrary-exponent LTE yields exact lifting and order by mutual divisibility, including zero exponent.73→68 lines including the new public helper; source bytes grow17, so no byte-compression claim. Joint power validation passes seven final calls plus one unchanged prerequisite restoration and a baseline; all15 old reports identical, new helper standard-three axioms. Independent full review passes |
| `patches/PellQuadratic.patch` | zo | `NativePellPower` | adopted as `88ebe8f66b`; a quadratic inequality at4^r≥16 replaces induction, retaining all nine public statements and doubled-coordinate data.4 lines removed without helper/import. Joint seven-call power suite passes, with ROOT's fresh Binary/scale clients and focuses separate. Two overbroad Lake builds were stopped, followed by explicit restoration of absent caches and successful narrow retries; interrupted/pre-elaboration results are not passes. Independent full review passes |
| `patches/02-power-fixed-point.patch` | zn | `CurrentControllerUnits2011` | adopted as `a9f8201893`; one generic monoid fixed-point induction propagates three checked literal power residues, including exponent zero.201→196 lines including the helper and removal of the direct finite-field import; no claim about transitive imports. Target, safe-controller client, both existing focuses and31-old-result comparison pass (five final calls after baseline and unchanged positions prerequisite). All old reports identical; independent full reviews pass |
| `patches/04-origin-reuse.patch` | zn | `CurrentWordOrigin2011` | adopted as `fc26c5f371`; specialize the existing source-reflection theorem, using the original support/alignment bound to exclude the reflected branch.118→111 lines, all old statements/data unchanged. Joint origin/dummy validation passes seven final calls including18-old-result comparison; independent full review passes |
| `patches/03-weighted-updates.patch` | zn, adapted | `CurrentDummyMutation2011` | adopted as `733d023d0a`; use `Function.apply_update` and the finite-sum update lemma directly, while retaining constructive equality cases for the Boolean bound.193→186 lines; the proposed shorter `forall_update_iff` proof was not used because it would add axioms to this previously axiom-free result. Joint seven-call suite above passes, all18 old reports identical; separate kernel controls confirm the constructive proof is axiom-free. Independent full review passes |

## Pending

| Proposal | Packet | Target | Note |
|---|---|---|---|
| guarded high-color fibers, `wang/proposals/boundary_fibers.patch` | o | `WangTiles942Boundary` | uncompiled proposal; claimed40 lines saved; retain high-color guard, initializer/reset colors and all seam tuples |

Packets g onward are triaged and adopted by the research session; the intake session only places
arrivals.

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
Remaining pending proposals and deferrals retain their separately recorded
scope; compiler validation of adopted groups does not certify those proposals.

Commits `4de06108b3`, `2ed7cc3ebb`, `2924138249` and `4261a5e353` remove638
physical lines across six modules (1909 to1271), bringing the reviewed series
to2788 net lines removed. A separately checked147-line coefficient-proof
prototype was not adopted: it took170.32s and produced a4953664-byte object,
with longer source and a larger object than the adopted d candidate. These
individual build timings are not controlled performance comparisons.

The five continuation groups above remove228 net lines across21 files,
including both new helpers, bringing the reviewed source-reduction series
to3016 lines. `intake_e13` authored the bridge and specification ports,
`v_finite_full_static` the scanner port, and ROOT the norm/quadratic ports.
Independent exact-final source review passes for all five groups. Equation
artifacts are unchanged.

The six source commits `57a5eed4d8`, `f1949d7be7`, `f3b6ad87d0`,
`4fc484d4c8`, `afbec38df7` and `8274c8f6b2` change six files from 1023 to 942
physical lines, removing 81 net lines and bringing the reviewed series from 3016
to 3097. This total fully charges the three-line increase in `RefinedPair`.
`v_finite_full_static` authored the refined-pair and register-pairing ports,
`intake_e13` the native power and step-down ports, and ROOT the rotation and
selective-degree ports. All old public axiom reports are unchanged, and all six
groups passed independent exact-final source review. The check counts above
describe their authors' actual compiler observations, not additional review
runs. Equation artifacts are unchanged; the pending Wang proposal and other
deferrals retain their separate scope.

Four further source commits `39a52d6353`, `80eabc57c8`, `ed32381986` and
`be154fa93b` reduce five modules from955 to799 lines, removing156 net lines
and bringing the reviewed series to3253. ROOT checks all56 old public headers
and35 complete definition regions against the immutable previous checkpoint;
they are unchanged. The five newly public Jones bridges expose existing proofs,
and the coefficient helper and its import are included in the line total.
The three validation groups have25 successful final Lean calls plus three
successful baseline audits; the one initial object-port inference failure is
recorded above. `intake_e13` authored the native span port,
`v_finite_full_static` the Jones reuse, and ROOT the coefficient and object
ports. All groups passed independent exact-final source review. The maintained
equation page was separately rechecked for decimal notation and distinct
unsubscripted unknowns; a fresh build reproduces its committed PDF byte for byte.

Five further source commits `91bb6ff650`, `52519f1cd6`, `8772c3b3a9`,
`bd12ef208c` and `1eb5d15000` reduce five modules from1276 to815 lines,
removing461 net lines and bringing the reviewed series from3253 to3714.
All56 old public theorem headers and13 definition headers are unchanged;
twelve complete definition bodies are literal, while the one changed proof
record is kernel-equal to its original by `rfl`. All61 old declaration axiom
reports are byte-identical. The final suites contain24 successful calls when
the shared residue-client build is counted once; preparatory builds and
baselines are separate. Two initial absent-cache queries stopped before
elaboration, and the coordinate candidate's dependent-type failure is recorded.
`v_finite_full_static` authored the common-modulus port, `intake_e13` the two
power ports, and ROOT the square/order ports. Every final source passed
independent full review. Equation artifacts remain unchanged. The separate
three-line padding proposal is unedited; it requires a much larger uncached
construction closure. The optional zo LTE-spectrum API and Pell inequality
ports remain unadopted in this batch.

Five further source commits `9c37c0868c`, `7f35ee6786`, `5bb366fcb8`,
`25feb7f728` and `88ebe8f66b` reduce six modules from759 to720 lines,
removing39 net lines and bringing this reviewed series from3714 to3753.
The three final suites have26 successful calls, counting shared Binary/scale
client evidence once. Preparatory original-source, baseline and cache-restoration
checks are separate, as are the preserved unsuccessful diagnostics and stopped
builds. ROOT authored the constructor/width ports, `v_finite_full_static` the
internal arithmetic ports, and `alternate_encoding_research` the LTE/Pell
ports. Exact-final independent full review passes for every group; all61 old
public declaration axiom reports are byte-identical. Equation artifacts remain
unchanged. Packing-rank simplification is still in baseline preparation and is
not included in these savings or validation claims.

Three further source commits `a9f8201893`, `fc26c5f371` and `733d023d0a`
reduce the units/origin/dummy modules from512 to493 lines, removing19 net
lines. Together with the preceding39-line batch, eight source commits reduce
nine modules from1271 to1213 lines, removing58 and bringing the reviewed
series from3714 to3772. The final suites contain38 successful calls, with
shared client evidence counted once. All110 old public axiom reports are
byte-identical. ROOT separately verifies93 old public theorem headers and19
complete definition blocks against immutable `40183b4bdc`; they are unchanged.
Every final source has independent full review. Packing-rank baseline work
still contributes no saving or final validation to these totals.

The degree certificates of `ShortSystem`, `ShortFrontier` and `ShortReducedStrong` were replaced
independently of these packets, by the `total_degree_bound` tactic in `TotalDegreeBound`.
