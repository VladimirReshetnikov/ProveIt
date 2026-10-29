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
| `patches/logic-proof-refinements.patch`, without redundant import | zr | `ObjectDivision`, `ObjectZeroTest` | adopted as `5bb366fcb8`; internal semiring cancellation replaces repeated gap reconstruction and a Boolean case split.7 lines removed, all formulas/definitions/types/imports unchanged. Eight final calls pass: two targets, two clients, three focuses and23-old-declaration comparison. Stale imported anonymous-instance names required14 unchanged cache refreshes and both original sources rebuilt before the coherent baseline; initial target/diagnostic failures preserved. Independent full review passes |
| `lte/prime-power-spectrum.patch`, composed over the existing guarded cast bridge | zo, adapted | `PrimePowerOrder` | adopted as `25feb7f728`; arbitrary-exponent LTE yields exact lifting and order by mutual divisibility, including zero exponent.73→68 lines including the new public helper; source bytes grow17, so no byte-compression claim. Joint power validation passes seven final calls plus one unchanged prerequisite restoration and a baseline; all15 old reports identical, new helper standard-three axioms. Independent full review passes |
| `patches/PellQuadratic.patch` | zo | `NativePellPower` | adopted as `88ebe8f66b`; a quadratic inequality at4^r≥16 replaces induction, retaining all nine public statements and doubled-coordinate data.4 lines removed without helper/import. Joint seven-call power suite passes, with ROOT's fresh Binary/scale clients and focuses separate. Two overbroad Lake builds were stopped, followed by explicit restoration of absent caches and successful narrow retries; interrupted/pre-elaboration results are not passes. Independent full review passes |
| `patches/02-power-fixed-point.patch` | zn | `CurrentControllerUnits2011` | adopted as `a9f8201893`; one generic monoid fixed-point induction propagates three checked literal power residues, including exponent zero.201→196 lines including the helper and removal of the direct finite-field import; no claim about transitive imports. Target, safe-controller client, both existing focuses and31-old-result comparison pass (five final calls after baseline and unchanged positions prerequisite). All old reports identical; independent full reviews pass |
| `patches/04-origin-reuse.patch` | zn | `CurrentWordOrigin2011` | adopted as `fc26c5f371`; specialize the existing source-reflection theorem, using the original support/alignment bound to exclude the reflected branch.118→111 lines, all old statements/data unchanged. Joint origin/dummy validation passes seven final calls including18-old-result comparison; independent full review passes |
| `patches/03-weighted-updates.patch` | zn, adapted | `CurrentDummyMutation2011` | adopted as `733d023d0a`; use `Function.apply_update` and the finite-sum update lemma directly, while retaining constructive equality cases for the Boolean bound.193→186 lines; the proposed shorter `forall_update_iff` proof was not used because it would add axioms to this previously axiom-free result. Joint seven-call suite above passes, all18 old reports identical; separate kernel controls confirm the constructive proof is axiom-free. Independent full review passes |
| `masks/patches/bit3_clear_of_residue.patch` | zl | `CurrentWordPadding2011` | adopted as `57dcc2a5ec` after the shared rank baseline made its original word dependencies available. Existing bit/remainder identities reduce224→221 lines without helper/import; arbitrary high multiples and the exact residue guard remain. Target, HighMask client, both existing focuses and11-old-result comparison pass (five final calls after separate baseline); all reports identical, changed bit lemma still choice-free. No failures/warnings or new prerequisite builds in this group; independent full review passes |
| `controller/patches/controller_hs_inline.patch`, with dead-tactic cleanup | zh, adapted | `CurrentControllerData2011` | adopted as `7f1081d5c6`; direct modular rewrites replace the private bookkeeping helper, retaining explicit kernel-residue hypotheses and opaque B/K.184→169 lines without helper/import overhead. Four final calls pass: target, unchanged current Units client, existing Data focus and49-old-result comparison; all reports identical. The first candidate passed too, then its new dead-tactic/focus warnings were removed and final scope rerun. Existing Units exponent warning remains; independent full review passes |
| `research/outer_seed/candidate.patch` | zz | `NativeOuterSeedConstruction` | adopted as `50d7e2133b`; reuse the already imported strict Pell index bound for the local hKr step.279→269 lines without helper/import, every other source byte literal including the31-field Seed structure. The original target was built explicitly before37-public baseline; target, positive-source client, existing focus and final37-report comparison pass (four final calls), all reports identical and no warnings. Exact inert archive candidate and independent full review pass |
| `arithmetic_candidates/fourblocks_certificate/fourblocks_certificate.patch` and `population/patches/rank_gt_twice_window.patch` | zs + zv, composed | `CurrentPackingRank2011` | adopted as `5187d9cb36`; the negative-q repunit certificate replaces the expanded integer bridge, and2u≤3u<2^(3u) supplies rank growth.138→122 lines without helper/import, all five subtraction guards and the single beta shift retained, including F=0. Five final target/parity-client/two-focus/10-old-result calls pass first try; all reports identical. Before editing,138 distinct named original/prerequisite builds and a separate original audit passed; two earlier missing-object failures remain separate. Independent full review passes |
| `rephase/patches/rephase-exact-field-rewrite.patch` | zv | `CurrentWordRephase2011` | adopted as `702687fc33`; rewrite the actual rotation equality directly in the two carry fields, retaining the scalar modular-transport block and the same carries/digits.122→116 lines without helper/import. Original target and baseline plus one unchanged generic-stride prerequisite are separate; five final target/client/two-focus/8-old-result calls pass, all reports identical. Existing focused exponent warning retained; independent full review passes |
| `safety/patches/positions_combined.patch`, with generic positive-stride cancellation | zv, adapted | `CurrentControllerPositions2011` | adopted with the population cleanup as `81e0f4daed`; the literal affine budget uses linear arithmetic, while injectivity cancels the original positive stride without unfolding dependent val terms.178→173 lines without helper/import or optional-support changes. The supplied injectivity proof failed; a checked coefficient-specific repair was superseded by generic cancellation. All seven joint final calls pass. Of31 old public reports,24 are identical and seven are strict subsets: six drop choice, injectivity drops choice and quotient soundness. The actual stdout comparison exit1 is retained; no artificial dependencies added. Independent full review passes |
| `population/patches/disjoint_add_lt.patch` | zv | `NativePackingPopulation` | adopted as the other file in `81e0f4daed`; rewrite the existing binary AND/OR sum identity directly.57→55 lines without helper/import, retaining zero width, strict representatives and unrestricted top block. Joint seven-call suite above passes; all four population reports identical. Combined pair235→228 lines, including the repaired generic injectivity proof; independent full review passes |
| `rank-upper.patch` | zw | `NativePellBootstrap` | adopted as `7e186e0c71`; an explicit nonnegative polynomial deficit replaces loose intermediate rank/mask estimates.671→657 lines without helper/import. All original source/port bounds remain, including negative mask ports allowed by the window theorem; the separate PortBox premises remain unchanged. Four final target/first-index-client/focus/38-old-result calls pass after baseline, all reports identical and no warnings. Entire6-field structure and old data remain literal; independent full review passes |
| `wang/proposals/boundary_fibers.patch` | o | `WangTiles942Boundary` | adopted as `a32e2a3d81`; two guarded colour-fiber helpers replace eight repeated case splits.201→161 lines including both helpers,84 bytes net. High-colour guard, halt head433, initializer south4, reset targets and nine square-west seam combinations retained. Ten final target/three-client/four-focus/generic-domain/15-old-result calls pass, all reports identical; new helpers standard-three axioms. Independent full review passes |
| `current-kernel-horner.patch` | zzb | `CurrentKernelResidues2011` | adopted as `276e19a689`; a verified whole-list accumulator replaces58 private length proofs,59 chunk certificates and assembly.426→183 lines,243 net including the new function and two proofs. The actual941 rows, physical reindexing, protected Start, controls and literal K binding remain exact. Six final production/Units-client/two-focus/16-old-result/new-API calls pass; all old reports identical, three new declarations use propext only. Same source limits/imports, existing Units warning retained. Independent full source/data/contracts review passes; no speedup claim |
| `patches/02-shifted-numerator.patch` | zx | `FreeCarrierRatio` | adopted as `52cd979b04`; the integer numerator envelope and a positive polynomial gap replace loose intermediate estimates, preserving signed Q and every free-carrier bound.501→491 lines/524 bytes without helper/import overhead; four final target/actual-client/existing-focus/65-public calls pass and all old reports are byte-identical. Original refresh and baseline are separate. Independent full review passes |
| compact structural size induction, adapted to retain the existing interpreter | zu, proof-only adaptation | `ExpressionSize` | adopted as `c87e01807b`; restricted simplification and explicit conjunction construction share the proof across constructors.90→80 lines/386 bytes, with all six definitions and the structure/derived instances literal. Six accepted target/three-client/focus/17-public calls pass, all reports byte-identical. Eight successful calls for axiom-rejected candidates, three failed production variants and one failed diagnostic remain separate. Independent full review passes |
| `patches/SignedPellResidue.patch` | zza | `SignedPellResidue` | adopted with the fresh-seed proof as `4f571a7890`; pass the existing additive natural norm through `Nat.sub_eq_of_eq_add'` directly to classification.102→99 lines/38 bytes, with all sign cases and old premises preserved. Joint nine-call final suite below passes; all five old reports identical. Independent full review passes |
| `patches/ThirteenFreshSeed.patch` | zza | `ThirteenFreshSeed` | adopted as the other file in `4f571a7890`; reuse the imported integer Pell norm twice.217→210 lines/204 bytes without helper/import overhead, preserving the negative ordinate and rank-three-mod-four guard. Both targets, four actual clients, both existing focuses and nine-old-public audit pass; all reports identical. The existing StepDown unused-hy warning remains. Independent full review passes |
| `patches/S1-realizer-dependency-inversion.patch` | zy, adapted | `Computability`, `DirectScalarEnumerator` | adopted as `59616d9d46`; derive computability from the existing literal scalar program, with a separate semantics module and a compatibility wrapper preserving the old import surface. Complete production modules608→395,213 lines removed; a31-line all-input compatibility check is included, yielding182 net. Fifteen final target/client/probe/focus calls pass and all62 old declaration reports are identical. Independent source, import-graph and evidence review passes |
| first-unit proof | t | `NativePellBootstrap` | adopted as `1e173a6849`; reuse nonzero Pell ordinate and exclude an integer between Q and Q+1.657→648 lines with signed ordinates and every premise unchanged. Joint ten-call final suite below passes; all old reports identical. Independent full review passes |
| `coordinate_gt_of_margin_pos` | zb | `MarginSeparation` | adopted as part of `1e173a6849`; use positivity and the existing absolute-square bound directly.141→133 lines without helper/import overhead, retaining arbitrary signed C and g≥0. Joint ten-call final suite passes; all old reports identical. Independent full review passes |
| `cyclic` integer-interval induction | u, adapted | `WangTiles942ResetRows` | adopted as part of `1e173a6849`; a single integer induction handles both directions with the original open-interval guards.162→150 lines without the proposal's extra import. Three targets, three clients, three focuses and59-old-public audit pass; all reports identical. Seventeen separate original Wang preparation, target, client and focus calls precede the baseline. Independent full review passes |
| `cyclic/patches/CurrentSouthShift2011.lean.patch` | o, adapted | `CurrentSouthShift2011` | adopted as `9602a7db90`; specialize the existing binary prefix and copy translation for offsets19 and20. Explicit numeral/cast simplification repairs the supplied patch.162→144 lines/615 bytes without helper/import overhead, preserving all nine copy equalities, Boolean bounds and selectors940/941/942. Four final target/client/focus/8-old-public calls pass, all reports identical. The exact packet and its first repair each failed and are retained separately;36 named prerequisite refreshes and the original baseline pass. Independent full review passes |
| `native-proofs/one-hot-support.patch` | k | `CurrentCellLabels2011` | adopted as `00e26fc130`; use `Finset.sum_le_one_iff` for arbitrary finite index types.311→294 lines. Six final target/three-client/focus/audit calls pass and all23 public axiom reports are identical; selected prior prerequisite refreshes and other precompiled objects are distinguished. Independent review passes |
| `patches/01-tail-cutoff.patch` | zd | `CurrentSelectorTail2011` | adopted as `0a8eb8938b`; derive the complementary cutoff with `not_congr` and simplify the successor step.335→322 lines with all guards unchanged. Four final target/client/focus/audit calls pass and all17 reports are identical. An initial overlay setup failure preceded the successful baseline; dependencies were precompiled. Independent review passes |
| `patches/04-deterministic-and-helical.patch`, composition hunks | ze | `ComposeRepresentation`, `DirectComposition` | adopted as `a69be9f233`; use function extensionality and `exists_eq_right` in the proof arguments.148→138 lines. The original full constructed representations equal the new ones by `rfl` for arbitrary inputs; six axiom reports are identical. Nine final calls and a recorded nine-call replay pass in an isolated overlay with precompiled dependencies. Independent review passes |
| `patches/04-deterministic-and-helical.patch`, helical hunk | ze | `WangTiles942HelicalQuotient` | adopted as `8e634984b5`; use period one along the helix to reach row zero.147→137 lines. Two prerequisite refreshes, original target/audit and four final target/client/focus/audit calls pass; all12 reports are identical. Four initial overlay path failures were corrected; other dependencies were precompiled. Independent review passes |
| `patches/01-unit-multiplication.patch` | zf | `ObjectOmegaSemiring` | adopted as `0947ccdb17`; reuse zero-left and successor-left multiplication with zero-left addition.120→107 lines. Six final target/three-client/focus/audit calls pass; all15 old reports are identical. Precompiled dependencies are reused. Independent review passes |
| `bridges/patches/WangTiles942FinishConstruction.lean.patch` | zi | `WangTiles942FinishConstruction` | adopted as `fde0d4e9db`; share the two halted tile proofs through one private conjunction helper.164→155 lines including the helper. Four final target/client/focus/audit calls pass; all24 public reports are identical. Precompiled dependencies are reused. Independent review passes |
| `cyclic/patches/CurrentCellCycle2011.lean.patch` | o | `CurrentCellCycle2011` | adopted as `7275f95fdc`; use the full-modulus identity for reachability and specialize existing arbitrary-base propagation.171→159 lines. Five final target/two-client/focus/audit calls pass; all25 reports are identical. Precompiled dependencies are reused; the Occupation client's broader closure was not fully refreshed. Independent review passes |
| `patches/03-bounded-complement.patch` | zd | `CurrentTileColors2011` | adopted as `9adc972817`; use bounded subtraction injectivity for both color equalities.104→100 lines while source grows38 bytes. Four final target/client/focus/audit calls pass; all five reports are identical. Nine affected prerequisites were refreshed before baseline and the changed cycle, Occupation and Coordinate modules were refreshed before final checks; other dependencies are precompiled. Independent review passes |
| `optional/permutation-injectivity.patch` | m | `WangTiles942Permutation` | adopted as `1e16302289`; compose finite injections and use `Fin.cons` injectivity.264→255 lines. Five final target/two-client/focus/audit calls pass; all33 old reports are identical. Other dependencies are precompiled. Independent review passes |
| `patches/02-variadic-fragments.patch` | p | `AnnotatedProofChecker` | adopted as `0c9a5e791e`; construct fragments for arbitrary premise lists, then specialize the existing zero- through three-premise results.376→366 lines including the new helper and removing a private lookup proof. Five final target/client/focus/variadic-probe/audit calls pass; all30 old reports are identical, and both new helpers use propext only. Dependencies are precompiled. Independent review passes |
| `encoding/StateNumber.patch`, adapted | v | `WangMachineEncoding` | adopted as `2e8dd29f57`; use direct Option cases and finite-value simplification without the proposed import.171→156 lines. Seven final target/four-client/focus/audit calls pass; all21 old reports are identical. An equivalence-based candidate passed but added Classical.choice to two declarations and was rejected. Other dependencies are precompiled. Independent review passes |
| `syntax/patches/list-head-monotone.patch` | y | `ObjectListHead` | adopted as `bfd57708b8`; rewrite a cons head and lift the existing left-pair bound by addition.129→121 lines. Four final target/client/focus/audit rechecks pass and all11 old reports are identical. Twenty-five earlier affected prerequisites and ten checker-affected prerequisites were refreshed; four earlier final calls are recorded separately. Other dependencies are precompiled. Independent review passes |
| `algebra_examples/QuarticCompiler.patch` | e | `QuarticCompiler` | adopted as `1918aaeb02`; combine the identical addition and multiplication completeness branches.448→440 lines, evaluator data unchanged. Six final target/four-client/audit calls pass; all31 old reports match. Other dependencies are precompiled. Independent review passes |
| `patches/B1-source-Y-row-one.patch` | zy | `NativePellBootstrap` | adopted as `9aace004ba`; derive the source Y lower bound directly from row one.648→640 lines with all premises unchanged. Five final target/two-client/focus/audit calls pass; all31 old reports match. Other dependencies are precompiled. Independent review passes |
| `machine/M1-act_next_none_iff.patch` | v | `WangMachineAction` | adopted as `35b702513f`; apply state-number injectivity to the next-state identity.119→112 lines, retaining the target bound. After refreshing `WangMachineEncoding`, five final target/two-client/focus/audit calls pass; all15 reports match. Other dependencies are precompiled. Independent review passes |
| `arithmetic/patches/sidon-moment.patch` and `local_candidates/patches/SidonPositions.lean.patch` | y + zm | `SidonPositions` | adopted as `4d9e4d7a30`; factor the square-sum difference and reuse unordered-pair uniqueness.168→157 lines including two tactic imports. Thirteen final affected-cone/focus/audit calls pass; all18 Sidon and31 Bootstrap reports match. Three separate calls check four attributed reports after one corrected root-setup failure. The unchanged SplitCertificate59 rebuild emits46 linter warnings without a comparable baseline log; other dependencies are precompiled. Independent review passes |
| `machine/M2-color_action.patch` | v | `WangMachineStep` | adopted as `b14017e756`; reuse the moved-head and read-write lemmas in the head cases.125→121 lines. After two prerequisite refreshes, five final target/two-client/focus/audit calls pass; all13 old reports match. Other dependencies are precompiled. Independent review passes |
| `patches/RatioReparameterization.patch` | zb | `RatioReparameterization` | adopted as `137b5440de`; cancel factors using the existing coprimality hypothesis.180→173 lines with signed integer cases and guards retained. Four final target/client/focus/audit calls pass; all19 old reports match. Other dependencies are precompiled. Independent review passes |
| `controller/patches/controller_coprime_cardinality.patch` | zh | `ControllerAuxiliaryChoice` | adopted as `1bc18914d4`; use the modular-cast zero criterion directly.50→44 lines. Four final target/client/focus/audit calls pass; both old reports match. Other dependencies are precompiled. Independent review passes |
| `patches/PolynomialRangeBounds.patch`, adapted | y | `PolynomialRangeBounds` | adopted as `5fe9c4795a`; reuse the already imported geometric-sum identity without adding an import.150→143 lines, retaining signed bounds. Six final target/three-client/focus/audit calls pass; all nine old reports match. Seven prerequisites were freshly rebuilt after reusing three authenticated early-padding outputs; other dependencies are precompiled. Independent review passes |
| `patches/modulus-reuse.patch` | a | `CurrentEarlyPadding2011` | adopted as `c414b8db6b`; specialize the existing modulus2048 selector congruence to16.311→305 lines. Thirty affected prerequisites were refreshed before baseline; eight final target/four-downstream/client/focus/audit calls pass and all19 old reports match. Three prerequisite modules emitted warnings without a comparable original full-cone baseline; other dependencies are precompiled. Independent review passes |
| `patches/NativeFieldCycles2011.patch`, retaining old imports | i | `NativeFieldCycles2011` | adopted as `43f5f376f9`; use surjectivity on the finite invariant even subset.111→104 lines. Five final target/client/two-focus/audit calls pass; both old reports match. The broader clients reuse precompiled intermediate dependencies. Independent review passes |
| `strip/WangTiles942HeadBounds.patch` | za | `WangTiles942HeadBounds` | adopted as `c0e20c2490`; derive both wall bounds from finite-coordinate bounds and square monotonicity.135→130 lines. Five prerequisites were refreshed before baseline; four final target/client/focus/audit calls pass. Seven reports match and both wall theorems strictly drop Quot.sound, with no added axioms. Other dependencies are precompiled. Independent review passes |
| `physical/patches/fin_pred.patch` | zh | `WangTiles942PhysicalOrder` | adopted as `8cb3a1aaf7`; use Fin.pred and Fin.succ_pred.155→148 lines. The old and revised full index values are equal by `rfl` for every input. Two prerequisites were refreshed; five final target/client/focus/probe/audit calls pass and all31 old reports match. Other dependencies are precompiled. Independent review passes |
| `patches/individual/trace-absolute-bound.patch` | u | `WangMachineTraceBounds` | adopted as `b0cc4adc6d`; use the absolute-value alternative directly.142→137 lines. Five machine/finish prerequisites were refreshed before baseline; four final target/client/focus/audit calls pass and all13 old reports match. Other dependencies are precompiled. Independent review passes |
| `patches/no-wrap-capacity.patch` | zr | `CurrentDummySafety2011` | adopted as `776133bf33`; use the preceding radix-power bound directly.213→208 lines, with the original guards retained. Four final target/client/focus/audit calls pass and all13 old reports match. The broader client graph was not refreshed and uses precompiled dependencies. Independent review passes |
| `patches/02-prime-factor-order.patch`, adapted | zd | `CurrentControllerData2011` | adopted as `66dafcc2b6`; share a private prime-factor order helper and use kernel-checked closed cases without a new import.169→162 lines. Eighteen affected prerequisites were refreshed before baseline; five final target/two-client/focus/audit calls and the additional RankStride client pass. All49 named old reports match; two unchanged anonymous instances are outside the probe. Ten further trace-dependent prerequisites were refreshed. Preparation warnings lack a comparable full-cone baseline; broader RankStride dependencies remain precompiled. The supplied plain-decide candidate failed. Independent review passes |
| `bridges/patches/WangTiles942TraceCycle.lean.patch`, repaired | zi | `WangTiles942TraceCycle` | adopted as `c74079d46b`; share temporal boundary cases with restricted simplification.182→178 lines. Five final target/two-client/focus/audit calls pass and all20 old reports match. The supplied candidate failed and is retained; an earlier Python setup failure has no retained log. Six authenticated prerequisite objects were reused; other dependencies are precompiled. Independent review passes |
| `patches/pell-fixed-index.patch` | z | `NativePellBootstrap` | adopted as `a8c12692bf`; use the existing fixed-index Pell estimates and monotonicity.640→636 lines. Five final target/two-client/focus/audit calls pass and all31 old reports match. Six authenticated Sidon-cone objects were reused; other dependencies are precompiled. Independent review passes |
| `syntax/patches/pairing-shell-threshold.patch` | y | `ObjectPairingInjective` | adopted as `5355cdf297`; a shell-midpoint helper collapses four branch combinations to two.104→100 lines including the new public helper, which omits the `succ_le` hypothesis. Twenty-four affected prerequisites were refreshed before baseline; six final target/two-client/focus/old-audit/new-helper calls pass and all six old reports match. The helper uses the standard three axioms; other dependencies are precompiled. Independent review passes |
| signed Pell residue sign split, independent adaptation | k-inspired | `SignedPellResidue` | adopted as `16ea41285c`; negate both modular alternatives together, without adding the proposed helper or import.99→95 lines. Five final target/two-client/focus/audit calls pass and all five old reports match. StepDown emits an unused-variable warning without a current baseline comparison; other dependencies are precompiled. Independent review passes |
| `patches/03-successor-certificate.patch` | p | `AnnotatedSyntaxGraphs` | adopted as `53b4259e9b`; share a successor-first certificate helper while retaining the impossible zero-output case.169→166 lines including the public helper. Nine affected prerequisites were refreshed after borrowing12 authenticated pairing outputs. Five final target/client/focus/zero-and-helper-probe/audit calls pass; all24 old reports including the decidable instance match, and the new helper uses propext only. Other dependencies are precompiled. Independent review passes |
| `units/patches/gamma_pos_from_coprime.patch` | zl | `CurrentControllerUnits2011` | adopted as part of `ef081fa2ae`; derive Gamma positivity from its existing coprimality.196→193 lines. The joint seven final target/two-focus/client/two-audit calls pass and all35 old reports match; the target exponent warning is byte-identical before and after. Independent review passes |
| `patches/controller-base-unit.patch` | zw | `CurrentControllerSubsets2011` | adopted as part of `ef081fa2ae`; derive the base unit from the odd block modulus.102→99 lines, with the proof comment updated. Nineteen SignedPell-affected prerequisites were refreshed before both baselines; joint final calls and old reports pass as above. Preparation warnings lack a comparable full-cone baseline; other dependencies are precompiled. Independent review passes |
| `patches/rotation-rephase.patch` | zr | `CurrentWordRephase2011` | adopted as `ed5538c38c`; unfold binary rotation and use the existing physical shift equality.116→113 lines, retaining the named Boolean premise. Five final target/client/two-focus/audit checks pass and all eight old reports match; a second baseline/final run borrows an authenticated prior packing object. The stronger proof leaves `hc` unused, producing a new warning; the focus and borrowed prerequisite also emit exponent warnings. The broader client chain remains precompiled. Independent review passes |
| `patches/coefficient-refactoring.patch`, NativeNinePolynomial52 hunk | c | `NativeNinePolynomial52` | adopted as `1eba5ee47c`; replace22 private row-specific naturality proofs with one finite case split.456→153 lines/−30587 bytes, all12 definitions and the public theorem statement retained. Sixteen affected prerequisites were refreshed before baseline; four final target/client/focus/audit calls pass and all20 old reports match. The consolidated theorem has an 8M local heartbeat limit; one target build observed23.26→14.13s and the olean grew396072 bytes, without a general speedup claim. Other dependencies are precompiled. Independent review passes |
| `projection-and-budget/patches/affine-budgets.patch`, repaired | k | `GraphSizeBounds`, `AffineBudget` | adopted as `8915bdc4a3`; share the witness-sum and depth-credit argument across three composition bounds.214→185 target lines plus a21-line helper, eight net lines saved. Twenty-eight affected prerequisites were rebuilt with the correct module root; seven final helper/target/two-client/focus/two-audit checks pass and all19 old reports match. The helper uses the standard three axioms. The supplied patch failed on three dead tactics; a wrong-root client run failed on private names and was replayed after rebuilding. Other dependencies are precompiled. Independent review passes |

Packets g onward are triaged and adopted by the research session; the intake session only places
arrivals.

## Deferred or not adopted

| Proposal | Packet | Reason |
|---|---|---|
| `patches/conditional-padding.patch` | a | changes a theorem interface in `NativePreliminaryCount2011` / `CurrentCount2011`, which the research session is editing |
| `patches/representation-naturality.patch` | d | superseded by a's `assignment-map.patch` |
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

Four more source commits `57dcc2a5ec`, `7f1081d5c6`, `50d7e2133b` and
`5187d9cb36` remove44 net lines. The complete twelve-commit batch reduces
thirteen modules from2096 lines to1994, removing102 and bringing the reviewed
series from3714 to3816. All56 final validation calls pass, counting shared
evidence once. All217 old public declaration reports are byte-identical;
161 old public theorem headers,27 entire definition blocks and the entire
31-field `Seed` structure remain literal against immutable `40183b4bdc`.
Every final source and the contracts used by its changed proofs passed
independent review. Original/prerequisite builds, baselines, diagnostics, superseded
successful candidates and interrupted/failed attempts are separately recorded
in the root review. The equation artifacts retain their decimal constant and
fourteen distinct unsubscripted unknowns.

Five source commits `702687fc33`, `7e186e0c71`, `81e0f4daed`,
`a32e2a3d81` and `276e19a689` reduce six modules from1655 to1345 lines,
removing310 net and bringing the reviewed series from3816 to4126. All32
final Lean calls pass. Of108 old public declaration reports,101 are
byte-identical and seven strictly reduce their axiom sets; none adds an
axiom. ROOT independently verifies90 old public theorem headers, ten entire
definition blocks and the entire6-field `PortBox` structure against immutable
`180e99fc75`; all are literal. Every exact-final source passed independent
full review. Preparation, baselines, the failed supplied injectivity proof,
its superseded checked repair and the intentional stdout difference for
strictly smaller axiom sets remain separately recorded. Equation artifacts
retain their checked decimal and distinct-name presentation.

After merging upstream `cbfdd02ce4` as `0ac0f529bf`, the narrowed decoder
import exposed an impractically slow tile certificate. `927256e3a5` makes
the old broad tactic dependency explicit in `WangTiles942Core`, preserving
the upstream arithmetic route and every other Core byte. This costs one
line: the final seven-module checkpoint is1885→1576,309 net removed, and
the reviewed series is4125. The earlier310-line/32-call figures describe
the pre-merge source batch above.

The repaired refresh completes96 successful scope commands: two preserved
fresh successes plus94 R1 calls, including88 affected project modules,
decoder focus,109 old-report comparisons and five new API reports. All109
comparisons are byte-identical, including Core's seven axiom-free reports.
Together with the unaffected bootstrap branch,147 old reports comprise140
identical reports and seven strict axiom subsets, with no additions. ROOT
also verifies116 complete old theorem headers,23 whole definitions, the
six-field PortBox and all Core structures/instances remain literal. The
three deliberate interruptions, malformed diagnostic-marker input and
pre-execution report-counter repair remain separate. The installed package
boundary and262 primary project objects are reused; this is not a whole
project replay. Durable inputs, results and original/corrected receipts are
in [the refresh bundle](../../reviews/lean-proof-simplification-309-refresh-20261026/BUNDLE.json).

The28 October checkpoint adopts `52cd979b04`, `4f571a7890` and `c87e01807b`:
four whole modules910→880 lines,30 net/1152 bytes removed, bringing the
reviewed series4125→4155. All19 accepted-source calls pass and all91 old
public reports are byte-identical. ROOT verifies37 complete old theorem
headers and20 whole definitions remain literal. Every final source passed
independent full review. The size proof's failed and axiom-rejected variants
are retained separately from the accepted proof and its unchanged footprint.

Upstream `6b774d6a65` is merged as `92fe8ac532`. Its data relocation changes
only LowMaskCoding and adds LowMaskData in the selected dependency closure.
Eleven separate post-merge calls freshly check all ten affected modules and
the combined91-report audit; all pass, and full report stdout is identical.
All220 source/configuration/equation pins and201 reused project objects
remain authenticated; four focus-only roots retain their earlier checks.
Installed packages remain a trusted precompiled boundary. No whole-project
or new upstream HA replay is claimed. Inputs, original/corrected candidates,
actual statuses and all144 archived entries are retained in
[the evidence bundle](../../reviews/lean-proof-simplification-20261028-evidence/BUNDLE.json).
The maintained decimal equation artifacts remain byte-identical.

The subsequent commits `59616d9d46` and `1e173a6849` remove211 net Lean
lines, including the enumerator compatibility wrapper and31-line regression,
bringing the reviewed series4366. All25 accepted final calls pass, and all121
old public reports are byte-identical. Original preparations and baselines
are separate. Existing project/package dependencies remain a precompiled
boundary outside the selected freshly checked cones. The equation artifacts
remain unchanged. Details and inputs are in [the evidence bundle](../../reviews/lean-proof-simplification-20261028-continuation-evidence/BUNDLE.json).

The adapted South-word proof `9602a7db90` removes another18 lines, bringing
this continuation to229 net and the reviewed series to4384. Its four
accepted final calls pass, with all eight old public reports byte-identical.
Combined with the prior two commits,29 accepted final calls pass and129 old
reports are byte-identical. The two earlier failed candidate calls and
preparatory rebuilds are separate; see [its evidence bundle](../../reviews/lean-proof-simplification-20261028-south-evidence/BUNDLE.json).


The next four commits remove50 lines across five modules, advancing the
reviewed series from4384 to4434. Twenty-three final target/client/focus/audit
calls and a separate nine-call composition replay pass. All58 recorded old
public axiom reports are byte-identical. These are scoped checks using
precompiled dependencies, not a whole-project build. The composition probe
also verifies equality of the old and new complete representation values by
`rfl`. Logs, source snapshots, command records and retained selector/helical setup
failure logs are in [the evidence bundle](../../reviews/lean-proof-simplification-20261028-four-proofs-evidence/BUNDLE.json).

The next four commits remove38 lines and1455 bytes across four modules,
advancing the reviewed series from4434 to4472. Nineteen final scoped
checks pass and all69 old public axiom reports are byte-identical. The tile
color check separately refreshes nine affected prerequisites before baseline
and three after the concurrent cell-cycle change. Other dependencies remain
precompiled; no full build is claimed. Inputs and recorded results are in
[the evidence bundle](../../reviews/lean-proof-simplification-20261028-four-more-evidence/BUNDLE.json).

The following three commits remove34 lines and698 bytes, advancing the
reviewed series from4472 to4506. Seventeen final scoped checks pass and all84
old public axiom reports are byte-identical. The annotated-fragment probe
also checks an arbitrary premise list and a four-premise list with repetition.
The rejected state-number candidate and its seven successful calls are kept
separate from the accepted proof. Dependencies outside the isolated targets
were precompiled; no full build is claimed. Inputs and results are in
[the evidence bundle](../../reviews/lean-proof-simplification-20261028-variadic-evidence/BUNDLE.json).

The list-head proof `bfd57708b8` removes eight lines and400 bytes, bringing
the reviewed series to4514. Four final rechecks pass and all11 old public
axiom reports match. After25 prior affected prerequisites, the concurrent
annotated checker change required a further ten-module refresh before the
final checks. Four earlier successful final calls are retained separately;
other dependencies are precompiled. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-listhead-evidence/BUNDLE.json).

The next three commits remove23 lines and998 bytes across three modules,
advancing the reviewed series from4514 to4537. Sixteen final scoped checks
pass and all77 old public axiom reports match. The machine-action validation
first refreshes its changed encoding dependency. Other project and package
dependencies are precompiled; no full build is claimed. Inputs and recorded
results are in [the evidence bundle](../../reviews/lean-proof-simplification-20261028-three-more-evidence/BUNDLE.json).

The Sidon proof `4d9e4d7a30` removes11 lines and524 bytes, bringing the
reviewed series to4548. Thirteen final calls rebuild or check the selected
Sidon-to-Bootstrap cone, and all49 old public reports match. Three additional
calls audit four attributed Sidon declarations; an initial root-setup failure
is retained separately. SplitCertificate59 emits46 linter warnings without a
comparable original-build warning log; remaining dependencies are precompiled.
Details are in [the evidence bundle](../../reviews/lean-proof-simplification-20261028-sidon-evidence/BUNDLE.json).

The next two commits remove11 lines and377 bytes, advancing the reviewed
series from4548 to4559. Nine final scoped checks pass and all32 old public
axiom reports match. Machine-step validation refreshed its encoding and action
prerequisites; other dependencies remain precompiled. Inputs and results are
in [the evidence bundle](../../reviews/lean-proof-simplification-20261028-step-ratio-evidence/BUNDLE.json).

The next three commits remove19 lines and399 bytes, advancing the reviewed
series from4559 to4578. Eighteen final scoped checks pass and all30 old public
axiom reports match. Early-padding validation refreshed30 affected
prerequisites; polynomial validation reused three of those authenticated
outputs and refreshed seven more. Three early-padding prerequisite modules
emitted warnings without a comparable original full-cone baseline; other
dependencies remain precompiled. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-choice-padding-evidence/BUNDLE.json).

The next three commits remove19 lines and637 bytes, advancing the reviewed
series from4578 to4597. Fourteen final scoped checks pass;40 old public axiom
reports match and two wall-bound reports are strict subsets, with no added
axioms. The complete old and new physical index values are equal by `rfl`.
Seven prerequisites were refreshed; other dependencies are precompiled,
including intermediate dependencies in the broad cycle clients. See
[the evidence bundle](../../reviews/lean-proof-simplification-20261028-cycle-wall-pred-evidence/BUNDLE.json).

The next two commits remove10 lines and309 bytes, advancing the reviewed
series from4597 to4607. Eight final scoped checks pass and all26 old public
axiom reports match. Five trace prerequisites were refreshed; the broader
dummy client graph and other dependencies remain precompiled. See
[the evidence bundle](../../reviews/lean-proof-simplification-20261028-trace-dummy-evidence/BUNDLE.json).

The controller order proof `66dafcc2b6` removes seven lines and279 bytes,
advancing the reviewed series to4614. Six final scoped target/client/focus/
audit calls pass and all49 named old axiom reports match; two unchanged
anonymous instances were outside that probe. Twenty-eight prerequisites were
refreshed, including ten for the additional RankStride client. Preparation
warnings have no comparable full-cone baseline and broader RankStride
dependencies remain precompiled. The supplied plain-decide candidate failed;
the kernel repair passed. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-controller-order-evidence/BUNDLE.json).

The next two commits remove eight lines and381 bytes, advancing the reviewed
series from4614 to4622. Ten final scoped checks pass and all51 old public
axiom reports match. Twelve previously refreshed prerequisite outputs were
authenticated and reused; other dependencies remain precompiled. The trace
packet's failed Lean candidate is retained, while an earlier Python setup
failure has no retained log. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-trace-pell-evidence/BUNDLE.json).

The pairing shell proof `5355cdf297` removes four lines and176 bytes,
including its new helper, bringing the reviewed series to4626. Six final
scoped checks pass and all six old public axiom reports match. Twenty-four
affected prerequisites were refreshed; other dependencies remain precompiled.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-pair-shell-evidence/BUNDLE.json).

The signed Pell proof `16ea41285c` removes four lines and102 bytes, bringing
the reviewed series to4630. Five final scoped checks pass and all five old
public axiom reports match. A StepDown client warning has no current baseline
comparison; other dependencies remain precompiled. See
[the evidence bundle](../../reviews/lean-proof-simplification-20261028-signed-or-evidence/BUNDLE.json).

The successor certificate proof `53b4259e9b` removes three lines and241 bytes,
including its new helper, bringing the reviewed series to4633. Five final
scoped checks pass and all24 old axiom reports match; the new helper uses
propext only. Nine prerequisites were refreshed after borrowing12 authenticated
outputs; other dependencies remain precompiled. See
[the evidence bundle](../../reviews/lean-proof-simplification-20261028-annotated-succ-evidence/BUNDLE.json).

The controller proofs `ef081fa2ae` remove six lines and216 bytes, advancing
the reviewed series to4639. Seven final scoped checks pass and all35 old
public axiom reports match. Nineteen SignedPell-affected prerequisites were
refreshed; preparation warnings lack a comparable full-cone baseline, and the
Units target warning is identical before and after. Other dependencies remain
precompiled. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-controller-units-subsets-evidence/BUNDLE.json).

The rephasing proof `ed5538c38c` removes three lines and138 bytes, bringing
the reviewed series to4642. Five final scoped checks pass in each of two runs,
with all eight old public axiom reports matching. The stronger proof leaves a
retained premise unused, producing a new warning; focus and previously built
prerequisite exponent warnings are separately recorded. The authenticated
borrowed object has a broader precompiled dependency chain. See
[the evidence bundle](../../reviews/lean-proof-simplification-20261028-rephase-evidence/BUNDLE.json).

The nine-variable coefficient proof `1eba5ee47c` removes303 lines and30587
bytes, bringing the reviewed series to4945. Sixteen affected prerequisites
were refreshed; four final scoped checks pass and all20 old reports match.
The consolidated proof uses an 8M local heartbeat limit and its olean is
396072 bytes larger in the recorded builds; single timing observations do
not establish a speedup. Other dependencies remain precompiled. See
[the evidence bundle](../../reviews/lean-proof-simplification-20261028-nine-polynomial-evidence/BUNDLE.json).

The affine-budget cleanup `8915bdc4a3` removes eight net lines and168 bytes,
including the new helper, bringing the reviewed series to4953. Twenty-eight
prerequisites were rebuilt with the correct module root; seven final scoped
checks pass and all19 old public axiom reports match. The failed supplied
candidate and earlier wrong-root client run are retained separately. Other
dependencies remain precompiled. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-affine-budget-evidence/BUNDLE.json).

The quotient/remainder certificate proofs `9aa66dfb9c` remove ten lines and
276 bytes, bringing the reviewed series to 4963. Both targets, one direct
client and two focused checks pass in baseline and final runs; all 16 old
public axiom reports match and the logs are warning-free. The checks reuse
compiled dependencies, including six whose sources have newer timestamps, so
they do not establish a fresh dependency closure. Baseline objects were later
overwritten, but their hashes and logs were recorded. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261028-divmod-evidence/BUNDLE.json).

The affine reflection proofs `a1b5f8f66b` remove 13 net lines and 453
bytes, bringing the reviewed series to 4976. Both changed targets, two focused
checks and two direct clients passed baseline and final checks; all 26 old
public axiom reports match. A named hypothesis remains for compatibility and
now produces an unused-variable warning. A broader client failed in both runs
because a cached dependency was absent; other dependencies remained cached.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-affine-reflection-evidence/BUNDLE.json)
for the failures and further limits.

The convolution factoring `44b9daa98b` removes 13 net lines and 205 bytes,
bringing the reviewed series to 4989. Baseline rebuilt 22 local modules and
final rebuilt seven affected modules; all 25 baseline and 11 final checks
passed, including matching focused outputs and 15 old public axiom reports.
No warnings were reported. HilbertTenthProblem and Mathlib dependencies remained
precompiled. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-convolution-evidence/BUNDLE.json).

The generated gap row identities `ead16b9c20` remove 148 net lines and
8425 bytes across the Lean source and its generator. Eight local prerequisites
were rebuilt; baseline and final target, client, focus, and 17 old public axiom
reports pass and match, including 26 existing client warnings. The refreshed
certificate emitted 46 warnings without a comparable fresh prerequisite
baseline; Mathlib remained precompiled. The initially considered `simp` proof
produced a much larger object; the adopted `dsimp` proof avoids that observed
cost. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-gap-source-evidence/BUNDLE.json).

The generated nine-variable coefficient maps `f941ac02db` remove 347 net
lines and 19424 bytes across two Lean files and their generators. Together
with the gap row proof, this brings the reviewed series to 5484 net lines.
Baseline and final targets, clients, focus checks and all 93 old public axiom
reports pass and match. Ten additional calls pass after borrowing nine
authenticated objects and rebuilding seven affected gap modules. Existing
client warnings match; two refreshed prerequisites emit warnings without a
comparable baseline. Other dependencies, including RatioReparameterization
and Mathlib, remain precompiled. The original heartbeat limits are unchanged;
target oleans grew by 512 and 544 bytes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-nine-maps-evidence/BUNDLE.json).

The generated kernel record bounds `ada40e5eb9` remove 692 net lines across
six Lean and generator files, bringing the reviewed series to 6176. All 13
baseline and final checks pass with identical logs and all 54 old public axiom
reports match. An authenticated refresh rebuilt 21 local modules and passed
seven focused and axiom checks, with matching comparable output. Thirty-two
objects were authenticated and reused; earlier local and external dependencies
remain precompiled. Existing heartbeat limits and warnings are unchanged. The
target oleans grew by 17640 and 9736 bytes in the recorded builds. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-kernel-records-evidence/BUNDLE.json).

The generated gap certificate row proofs `7441eed24d` remove 386 net lines
across the source and generator, bringing the reviewed series to 6562. Four
baseline and final target, client, focus and axiom checks pass; all ten old
public axiom reports and the client and focus logs match. Target warnings fall
from 26 to three pre-existing warnings. Fifty-one local objects were
hash-authenticated; earlier local and external dependencies remain precompiled.
The target object grew by 307392 bytes in the recorded builds. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261028-gap-certificate-evidence/BUNDLE.json).

The current kernel mass reuse `0126040276` removes 316 net lines across the
target and prerequisite comment, bringing the reviewed series to 6878. The
prerequisite was rebuilt; target, focus, two direct clients and 24 old public
axiom reports pass in baseline and final runs with matching output and no
warnings. Three ancestor sources have newer timestamps than their cached objects,
and external dependencies remain precompiled. Newly merged
`ArithmeticConstructionBound` transitively imports the comment-only prerequisite;
it was not checked. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-kernel-mass-evidence/BUNDLE.json).

The Wang data chunk assembly `93240c46a2` removes 88 lines and 5485 bytes,
bringing the reviewed series to 6966. The decoder prerequisite was freshly
rebuilt; target, table and core clients, corrected boundary checks and all 21
old public axiom reports pass in baseline and final runs with identical logs and
no warnings. The initial boundary probe failed on an unqualified namespace;
both failures and the corrected checks are retained. BusyBeaver and Mathlib
remain precompiled. The newly merged arithmetic modules were not tested. The
target object shrank by 1333584 bytes in the recorded builds. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261028-wang-chunks-evidence/BUNDLE.json).

The matrix-free kernel mass reuse `6e09808cb8` removes 314 lines, bringing the
reviewed series to 7280. Eleven prerequisites were rebuilt; target, client,
focus and 24 old public axiom reports match in baseline and final checks with
no warnings. The focused Matrix-name test passes; a Foundation co-import could
not run in this Lake environment. Earlier local and external dependencies remain
precompiled. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-mf-mass-evidence/BUNDLE.json).

The selector-tail reuse `0e5e05a7c5` removes 173 lines and 7692 bytes, bringing
the reviewed series to 7453. Target, focus, direct client and 17 old public
axiom reports match with no warnings. Required new prerequisites were rebuilt
or authenticated; five other sources have newer timestamps than their cached
objects and external dependencies remain precompiled. The individual prerequisite
shell commands were not recorded. An initial numeric proof added standard axioms;
the original kernel-decided proof was restored. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-selector-tail-evidence/BUNDLE.json).

The Pell transport reuse `e4c9f49314` removes 55 net lines, bringing the
reviewed series to 7508. Both targets, two focused checks and 29 old public
axiom reports pass and match; both promoted helpers use the standard three
axioms. The auxiliary baseline was replayed from the original snapshot after an
overlapping source read. NativePellBootstrap and SignedPellResidue remain older
cached ancestors, and two direct construction clients were not tested. Target
exit statuses were observed in the tool output rather than recorded in JSON. See
[the evidence bundle](../../reviews/lean-proof-simplification-20261028-pell-transport-evidence/BUNDLE.json).

The shared literal representation `43c60fcabd` removes 207 net lines across
two modules, bringing the reviewed series to 7715. Corrected snapshot baseline
and final targets, focus, radix client and all nine old public axiom reports
pass and match; five new or promoted helper reports pass. Seven prerequisites
were refreshed and three objects authenticated. Earlier local, Foundation and
Mathlib chains remain precompiled; ArithmeticCurrentConstruction2011 and the
newly merged ArithmeticConstructionBound were not checked. An earlier baseline
used edited sources and is excluded. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-literal-representation-evidence/BUNDLE.json).

The matrix-free physical-position injectivity proof `1012776b84` removes five
lines, bringing the reviewed series to 7720. Baseline and final target, direct
client and all 33 old public axiom reports pass with identical logs; client
object hashes match. Eleven local source/import/object pins were verified, while
earlier local and external dependencies remain precompiled. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261028-mf-permutation-evidence/BUNDLE.json).

The Jones quartic correctness reuse `ca84549030` removes 13 net lines across
three modules, bringing the reviewed series to 7733. Four affected prerequisites
were rebuilt; targets, a direct client, focused checks and all 58 old public
axiom reports pass with matching logs and no warnings. Other project and
external dependencies remain precompiled. An initial all-trans prototype timed
out, but its empty log and overwritten source have no standalone status record.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-jones-quartic-evidence/BUNDLE.json).

The generated consumer-table proof `b696a79f7c` removes 26 net lines and 557
bytes across the shared helper, three generated circuits and their generator,
bringing the reviewed series to 7759. All baseline/final targets, rechecked
prerequisites and clients, focused checks and 176 old public axiom reports pass;
comparable logs match. Both initial joint-client runs exceeded the 6 GB Lean
memory cap; sequential replays passed with a 9 GB cap. Earlier overwritten
client records are excluded in favor of contemporaneous reruns, and the unchanged
semantics prerequisite emits five matching warnings. Mathlib and other project
dependencies remain precompiled. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-consumer-table-evidence/BUNDLE.json).

The HA decision proof reuse `8c0a3a9f61` removes 36 net lines, bringing the
reviewed series to 7795. Twenty-one baseline project modules were rebuilt;
final targets, two focused checks, two direct clients and all 37 old public
axiom reports pass with matching logs and no warnings. Current PACore was
authenticated from a prior refresh; Foundation, FirstOrder, AckermannHFCore,
Mathlib and other earlier dependencies remain precompiled. The new-helper probe
status was observed but not separately recorded in JSON. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261028-ha-decisions-evidence/BUNDLE.json).

The DAG RHS degree reuse `e374d0dd9d` removes ten net lines and 503 bytes,
bringing the reviewed series to 7805. Two prerequisites were rebuilt and four
prior objects authenticated; targets, a direct client, focused checks, 56 old
public axiom reports and two inferred-instance probes pass with matching output
and no warnings. Other project and external dependencies remain precompiled;
helper and instance-probe statuses were observed but lack separate JSON records.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-dag-rhs-degree-evidence/BUNDLE.json).

The shifted padding suffix reuse `423704157f` removes ten net lines across
three modules, bringing the reviewed series to 7815. Baseline and corrected
final affected modules, focuses, clients and 73 old public axiom reports pass.
Three existing ArithmeticCellLocal warnings differ only by line number. An
initial helper name caused an ambiguous focus check; its renamed version and
boundary probes pass. The client was tested from its original pinned snapshot
while a separate mask edit was in progress. Earlier local and external
dependencies remain precompiled. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-padding-shift-evidence/BUNDLE.json).

The matrix-free mask proof reuse `f405dc9f52` removes 19 net lines, bringing
the reviewed series to 7834. Original-snapshot baseline and final targets use
the same authenticated corrected padding/cell objects; all 31 old public axiom
reports, boundary checks and actual Foundation.Vorspiel.Matrix co-imports pass
with matching logs. ArithmeticCellTransfer could not be checked because its
ArithmeticCyclicWord object was missing. Earlier dependencies remain precompiled,
and the prerequisite build and failed direct-client probe statuses were observed
rather than separately recorded in JSON. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-mask-reuse-evidence/BUNDLE.json).

The reflected-geometry reuse `30decae790` removes 16 lines and 465 bytes,
bringing the reviewed series to 7850. Target, two clients, focus and 27 old
public axiom reports pass with matching logs and no warnings. The new
prerequisite object was authenticated against a successful build using the
latest matrix-free permutation. Five other local sources have newer timestamps
than cached objects, and earlier dependencies remain precompiled. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-reflected-reuse-evidence/BUNDLE.json).

The binary half-bound reuse `dfc1b71ea6` removes seven net lines, bringing the
reviewed series to 7857. Population, carry and rank modules, focus, Repunit
client, 45 old axiom reports and seven instance reports pass with matching
output. The unchanged carry prerequisite emits six identical warnings; earlier
Foundation and project dependencies remain precompiled. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261028-binary-half-evidence/BUNDLE.json).

The quadratic quotient certificate reuse `baa756510e` removes seven net
lines, bringing the reviewed series to 7864. Four DAG objects were authenticated
and 22 affected prerequisites rebuilt. Baseline and final target, direct client,
two focuses and all 16 old public axiom reports pass with matching logs and no
warnings. The borrowed DAG semantics build previously emitted five matching
warnings; four earlier sources have newer timestamps than cached objects and
external dependencies remain precompiled. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-divmod-reuse-evidence/BUNDLE.json).

The encoded-word degree reuse `803467264d` removes ten net lines across four
modules, bringing the reviewed series to 7874. All 21 affected local modules
were rebuilt in both phases; four focused checks and 50 old public axiom
reports pass with matching logs and unchanged existing warnings. Fifty-one
prior objects and the current gap certificate were authenticated; earlier
local and Mathlib dependencies remain precompiled. The client driver was edited
after baseline, though its original command/status records were retained;
generator and helper-probe statuses were observed without separate JSON records.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-encoded-degree-evidence/BUNDLE.json).

The matrix-free reflected-geometry reuse `300d4cb167` removes 20 net lines,
bringing the reviewed series to 7894. Targets, a direct client, 21 old axiom
reports and actual Foundation matrix co-imports pass with matching logs. Eight
missing prerequisites were rebuilt; one unchanged prerequisite emitted a
warning without a paired fresh baseline. Initial missing-object attempts were
corrected and retained. Earlier dependencies remain precompiled. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-mf-reflected-reuse-evidence/BUNDLE.json).

The quadratic predecessor proof `06786bfce1` removes seven net lines, bringing
the reviewed series to 7901. Targets, two clients, focus, boundary checks and
26 old axiom reports pass with matching logs. Twenty-two prior refreshed
prerequisites and four authenticated DAG objects were reused; four earlier
sources have newer timestamps than cached objects. Failed preliminary probes
were retained, and the recorded graph was corrected after review. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-pred-certificate-evidence/BUNDLE.json).

The clean-band list proof `b5a09e98e8` removes five net lines, bringing the
reviewed series to 7906. Twenty-one affected prerequisites were refreshed;
target, two clients, focus and ten old axiom reports pass with matching logs.
One existing client warning matches; preparation warnings lack a comparable
fresh pre-preparation run, and earlier dependencies remain precompiled. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-clean-bands-evidence/BUNDLE.json).

The standard numeral cast reuse `f5a4267229` removes 18 net lines and 751
bytes across four existing modules and a new shared helper, bringing the reviewed
series to 7924. Original-snapshot and final targets, two selected direct clients,
104 named old axiom reports and an actual Foundation matrix co-import pass.
The replay captured its effective Lean path and object hashes. This also checks
the previously unavailable ArithmeticCellTransfer client against the current
matrix-free mask change. Two other PackingCells clients remain unchecked;
earlier local and external dependencies remain precompiled. WangTable first
exceeded the 6 GB Lean cap and passed at 9 GB; existing warnings and corrected
preliminary failures are recorded. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-standard-casts-evidence/BUNDLE.json).

The implication-transfer reuse `f77baa3490` removes six net lines, bringing the
reviewed series to 7930. Isolated baseline and final target builds and the
focused client pass; all ten target/client axiom reports match. The 37 local
prerequisite source/object pairs were hash-audited, with 29 refreshed and eight
historical pinned objects. Foundation, FirstOrder, most PAHF and external
dependencies remain precompiled. Two broader clients remain unverified
because prerequisite objects were unavailable; failed attempts are retained.
Independent review passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-ha-implication-evidence/BUNDLE.json).

The shared gate induction `bdb9679e73` removes 27 net lines, bringing the
reviewed series to 7957. Both target versions and four direct clients pass
after rebuilding 12 local prerequisites and two additional client prerequisites;
all 44 expanded public, instance and structure axiom reports match. The fifth
direct client, EquationFromRep, remains unverified because its JonesSyntax
closure has stale cached dependencies. The unchanged Paper1982 prerequisites
emit 23 warnings without a paired baseline; Mathlib is precompiled. The build
receipt reconstructs commands and uses a later captured Lake environment suffix.
Independent review passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-quartic-gates-evidence/BUNDLE.json).

The conditional list lookup reuse `66f7e490ff` removes 14 net lines and 599
bytes including the helper, bringing the reviewed series to 7971. Both normal
and cell targets pass before and after against refreshed dependencies; all 89
public and generated axiom reports match. Three normal, nine matrix-free and
one cell direct clients pass, as does a Foundation Matrix co-import. The
matrix-free and external dependencies remain cache-bounded. Three existing
cell warnings match apart from locations; five unchanged refreshed prerequisites
emit 51 warnings without paired baselines. Target command/path receipts were
reconstructed from observed calls. Independent review passes. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261028-list-getd-evidence/BUNDLE.json).

The matrix-free evaluation proof `f1706b3f77` removes six lines, bringing
the reviewed series to 7977. Baseline and final targets, ArithmeticConstructionUnit
and all 17 public axiom reports pass with matching logs after rebuilding 16
target and ten additional client prerequisites. Foundation PRF was checked
against its clean pinned checkout; Mathlib and external inputs remain
precompiled. Four unchanged prerequisites emit nine warnings without paired
baselines. Independent review passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-mf-evaluate-sum-evidence/BUNDLE.json).

The one-element Fin proof reuse `aec7bcf3db` removes 12 lines in three
represented iteration modules, bringing the reviewed series to 7989. Both
versions of all three targets and six direct clients pass; all 97 named
declaration and instance axiom reports match. Independent review verified
1,327 distinct historical source/object/manifest pins. Foundation, BusyBeaver
and other dependencies remain authenticated precompiled inputs. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-fin-one-evidence/BUNDLE.json).

The ordinary evaluation proof `de2fe5efbf` removes six more lines, bringing
the reviewed series to 7995. Both target versions, two direct clients and all
19 public axiom reports pass with matching logs. Six prerequisites were rebuilt
and 22 relevant prior source/object pairs authenticated; the remaining project
and external inputs are precompiled. One existing units warning matches.
Independent review passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-normal-evaluate-sum-evidence/BUNDLE.json).

The trace Fin 1 reuse `cad556929a` removes four lines, bringing the reviewed
series to 7999. Both target versions, the direct client and all 37 public
axiom reports pass after refreshing 26 affected prerequisites. The 132 selected
local dependency objects were classified: 97 historical pins, nine recent
kernel builds and 26 refreshed descendants; external packages remain precompiled.
Nine target and six client warnings match after location normalization. Four
unchanged refreshed prerequisites emit 16 warnings without paired baselines.
WangTable first failed at 6 GiB and passed at 10 GiB; the first refresh was
deliberately interrupted to repair its dependency closure. Independent review
passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-fin-one-trace-evidence/BUNDLE.json).

The Wang initialization proof cleanup `f82f4047ce` removes four lines,
bringing the reviewed series to 8003. Paired target, focused check, four
direct clients and 23 public axiom reports pass with matching logs. The
initialization prerequisite was rebuilt, and Wang core, tile data and machine
source objects matched recent receipts. Six BusyBeaver inputs and further
tile-client prerequisites remain historical precompiled boundaries without
exact receipts; the older graph is not wholly current, but affected clients
were rebuilt and current tile data matched a recent receipt. Independent
review passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-wang-initialization-evidence/BUNDLE.json).

The shared reflected bounds `777a764cf8` remove 50 net lines across four
modules, bringing the reviewed series to 8053. Paired target builds and four
representative clients pass, as do 160 existing public, exported and generated
axiom comparisons; the two new helpers use the standard three axioms. Eighteen
prior objects were authenticated and three affected modules rebuilt; the
changed-object descendants are covered in the 59-node local graph. Remaining
historical and external inputs are precompiled, and other direct clients remain
unchecked. Three existing cell warnings match after location normalization;
the initially failed normal and missing-MF prototypes are retained. Independent
review passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-reflected-shared-evidence/BUNDLE.json).

The carry lookup sharing `0ce4bf0bc5` removes eight net lines, bringing the
reviewed series to 8061. Both targets, two direct clients, two affected bounds
modules and two focused checks pass in both phases; all 39 named and 13
generated axiom reports match, and the new helper has the standard three axioms.
All 26 local graph nodes match authenticated receipts and all 11 descendants of
refreshed HTP seeds were rebuilt. Five warnings in unchanged HTP preparation
lack paired baselines; external packages are precompiled and the umbrella import
was not rebuilt. Independent review passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-carry-map-evidence/BUNDLE.json).

The additional Fin 1 rewrites `ebaa26c8c9` remove 12 lines across Pell,
repunit and tape modules, bringing the reviewed series to 8073. Both target
versions and seven direct clients pass with matching warning-free logs; all
91 named public axiom reports match. All 336 non-target nodes in the three
inventories match current source/object hashes and exact receipts; Foundation,
Mathlib and historical inputs remain precompiled. ArithmeticBinaryCarry emits
six unpaired prerequisite warnings. An initial tape-client attempt lacked
TapePrefix; the prerequisite was built and the client passed, with its prefix
command/path receipt reconstructed. Independent review passes. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-fin-one-more-evidence/BUNDLE.json).

The Pell divisibility reuse `10befdc6ac` removes eight net lines, bringing
the reviewed series to 8081. Both target versions, two direct clients and
all 14 public axiom reports pass with identical warning-free logs. Two immediate
prerequisites were rebuilt and 100 selected source/object pairs matched
authenticated receipts; other dependencies remain precompiled. The only new
transitive module is Mathlib.Algebra.Ring.Divisibility.Basic, whose 510-job
Lake closure passed a read-only freshness check. Independent review passes.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-pell-dvd-evidence/BUNDLE.json).

The Wang rail cardinality rewrite `8a7ecedcb2` removes 14 lines, bringing
the reviewed series to 8095. Both targets, the focused check, seven direct
clients and 32 public/generated axiom reports pass with matching logs. The
target cone matches nine recent kernel receipts and three freshly rebuilt
core/initialization/encoding prerequisites. CurrentOccupation passes only
on a cache-bounded 89-node graph with six source-newer objects; other external
and historical caches remain precompiled. Earlier missing-encoding failures
and successful reruns are retained. Independent review passes. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-wang-rail-card-evidence/BUNDLE.json).

The shared selector bounds `9da35a0562` remove 37 net lines across four
modules, bringing the reviewed series to 8132. Paired target builds and four
representative clients pass; all 162 existing public, exported and generated
axiom reports match, and both new helpers use the standard three axioms. All
55 selected local prerequisites match the preceding reviewed reflected-graph
objects; external packages and previously identified historical client
dependencies remain precompiled, and other direct clients remain unchecked.
Three existing cell warnings match after location normalization. The first
prototype hit recursion limits and introduced an extra warning; both are
retained separately. Independent review passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-selector-shared-evidence/BUNDLE.json).

The split/gap target-image rewrite `9e9c79e209` removes 18 lines, bringing
the reviewed series to 8150. Both target versions, two direct clients, two
existing focused checks and all five public axiom reports pass with matching
logs. The 73-node graph and all changed-object descendants were checked; 21
affected modules were rebuilt and ten HTP seeds authenticated. Fifteen
warnings in three unchanged refresh prerequisites lack paired preparation
baselines; other HTP and Mathlib inputs remain precompiled. The earlier
cache-bounded prototype is separate. Independent review passes. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-source-carry-image-evidence/BUNDLE.json).

The Wang strip conditional rewrite `ebd0e9e513` removes eight lines,
bringing the reviewed series to 8158. Both target versions, all three direct
clients and 15 named/generated axiom reports pass with identical warning-free
logs. Three prerequisites were rebuilt and all 24 local dependency nodes
match current source/object hashes and previous or new receipts; external
packages remain precompiled. Independent review passes. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261028-wang-strip-split-evidence/BUNDLE.json).

The gcd remainder sharing `83a30a00a3` removes five lines, bringing the
reviewed series to 8163. Both target versions, the focused check and two direct
production clients pass; all 26 environment-enumerated public/generated axiom
reports match, including six matching warnings for printed generated auxiliaries.
All 98 selected source/object pairs match prior receipts and 102 inventory import
edges were checked. The further downstream ArithmeticPellIntegralSolution was
not rebuilt; Foundation, Mathlib and historical inputs remain precompiled.
Independent review passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-gcd-remainder-evidence/BUNDLE.json).

The shared modular reflected-source proof `b1ddb64112` removes 14 net
lines, bringing the reviewed series to 8177. Both target versions, four
representative clients, the actual Foundation Matrix co-import and all 48
public axiom reports pass with matching logs. Both import sets gain only the
new helper, which uses the standard three axioms. All 55 selected prerequisites
match the prior reviewed graph; other client and external inputs remain
precompiled, and additional direct clients were not exhaustively rebuilt.
Initial path-shadowing and bare-Matrix probe failures are retained separately.
Independent review passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-reflected-source-evidence/BUNDLE.json).

The bounded-exit rewrite `b16f744e3b` removes 15 lines, bringing the
reviewed series to 8192. Both target versions, the sole direct client and all
38 public/generated axiom reports pass; three lazy equation declarations were
materialized during review. The 158-node graph and 156 selected dependency
pairs match authenticated receipts, with no conflicts across 1,265 merged
cache files. EnumBoundTower was rebuilt; its command/path receipt was
reconstructed. External inputs remain precompiled and five matching warnings
come from axiom probes. The object grows by 576 bytes despite the source
reduction. Independent review passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-bounded-exit-evidence/BUNDLE.json).

The bounded outer-seed sharing `39c8dbe329` removes 120 net lines, bringing
the reviewed series to 8312. Both targets, explicit old-interface checks,
48 materialized old declaration/equation axiom reports and nine defining
equation outputs match; both production Assembly clients and six Assembly
axiom reports also pass. The seed cone uses 17 current rebuilds and eight
verified first-pass objects; 54 additional Assembly prerequisites were rebuilt
and all 162 phase/local source/object pins checked. The broader
ArithmeticConstructionBound client remains unverified because its separate
ArithmeticConstructionZero prerequisite was absent. External inputs remain
precompiled; stale PAHF.PASyntax was excluded as unreachable. Assembly and
seed preparation emitted 53 and five warnings without paired baselines; 11
generated-auxiliary axiom warnings match, and the Foundation freshness check
replayed 40 warnings. Initial missing Vec/PAHF failures are retained separately.
Independent review passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-outer-seed-sharing-evidence/BUNDLE.json).

The doubled-clause mask reuse `1802229762` removes 20 net lines, bringing
the reviewed series to 8332. Paired target builds, four ordinary clients,
the matrix-free cell-label client and the Foundation Matrix co-import pass.
All 31 surviving ordinary declaration and forced-equation axiom reports
match. Two autogenerated `mask_iff` proof auxiliaries disappear; repository
source search found no references. `mask.eq_1` still matches when materialized.
The import set gains only the independent matrix-free mask module. Of 64
selected local prerequisites, 56 match recent receipts; Carrier65, ShortSystem,
ShortCircuit, ShortEquation, ConsecutivePell, TotalDegreeBound,
CarrierRankBounds and ThirteenCarrier remain historical precompiled boundaries.
External inputs remain precompiled and other clients were not exhaustively
rebuilt. The ordinary target object falls from 501728 to 424528 bytes; single
timing observations do not establish a speedup. Independent review passes.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-doubled-mask-evidence/BUNDLE.json).

The Wang permutation proof reuse `0ffb53a8d5` removes 105 net lines,
bringing the reviewed series to 8437. Paired targets, two downstream clients,
246 surviving declaration axiom reports and seven forced defining equations
match. Twenty-nine autogenerated auxiliaries disappear; no tracked source
references or baseline default simp registrations were found. All seven
local target prerequisites match prior receipts and both overlays. The
ordinary permutation/Foundation Matrix co-import already fails in both phases;
the matrix-free co-import passes in both orders. External inputs remain
precompiled, and complete fresh builds and unrestricted downstream consumers
were not tested. The first paired prototype and graph target source hash are
superseded by the final receipt. Independent review passes. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261028-wang-permutation-sharing-evidence/BUNDLE.json).

The joint bisimulation clock induction `2e5b3dba2e` removes 31 net lines,
bringing the reviewed series to 8468. Both targets, compatibility examples,
the reverse production module, the forward ArithmeticRuntimeBound215 client
and its six declaration reports pass; 13 old namespace declaration and axiom
reports match. The forward check rebuilt 25 affected prerequisites, with 113
borrowed project objects and 405 compiled companions authenticated. The
broader ArithmeticRefutationHaltBound client remains unverified after initial
attempts lacked ArithmeticProofWordBound. Earlier missing dependency and
companion failures, and the interrupted refresh, are retained. Foundation,
Mathlib and other authenticated inputs remain precompiled. Independent review
passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-bisim-joint-clock-evidence/BUNDLE.json).

The shared bounded enumerator recursion `b22cefad65` removes 11 net
lines, bringing the reviewed series to 8479. Paired target and compatibility
checks pass, all three complete program records are definitionally equal by
`rfl`, and 253 retained declaration axiom reports match. Their printed
bounded-run equations now name the shared proof. Three autogenerated proof
auxiliaries disappear, with no tracked source references or baseline default
simp registrations. A later focused refresh rebuilt FirstOrder.Fol and all
19 affected local modules for GraphSizeBounds; paired client and proof checks
pass with 151 local and 71 direct external object pins per phase. Six shared
TarskiComplete warnings and 27 matching generated-auxiliary warnings per axiom
probe remain; the initial missing-overlay failure is retained. Unaffected local
and transitive package inputs remain precompiled, and Bridge, ExplicitZFC and
NativeZFC were not rebuilt in the focused refresh. Independent reviews pass.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-enumerator-recursion-evidence/BUNDLE.json).

The first-norm Pell descent reuse `6d9e6e43a7` removes 54 net lines,
bringing the reviewed series to 8533. Paired target builds, FirstIndex and
PowerRecovery clients and their focused checks pass; 32 public and 17 private
declaration type and axiom reports match. All 30 phase-local source/object
pins and their prior dependency receipts were independently checked. Eight
generated-auxiliary warnings match per public axiom probe; an unsuccessful
private-name text probe is retained alongside the successful metadata probe.
The target object shrinks by 346904 bytes. Foundation, Mathlib and other
inputs remain precompiled, and clients beyond the tested chain were not
rebuilt. Independent review passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-pell-firstnorm-sharing-evidence/BUNDLE.json).

The standard radix bound reuse `2b254d6c2e` removes five lines, bringing
the reviewed series to 8538. Both targets and the direct RankForcing client
pass with matching empty logs. All 31 existing declaration types and axiom
reports, plus the materialized `inS` equation, match. The base-one case is
checked separately; direct prerequisite hashes match prior or freshly
refreshed receipts. Interface probe logs are retained without separate command
receipts. Transitive dependencies remain cached or partly refreshed, and no
full clean build is claimed. The target and client records and logs were
independently checked. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-mask-digit-bound-evidence/BUNDLE.json).

The semiring gate branch sharing `28a62dffb9` removes 21 net lines,
bringing the reviewed series to 8559. Paired targets and the direct
QuarticSemiring client pass; all 204 existing declaration types and axiom
reports and ten materialized equation theorems match. The QuarticCompiler
prerequisite matches prior receipts, but NaturalExpressionSemiring is a
precompiled object without a matching source/object receipt; package and
other transitive inputs remain cached. Interface probes have matching logs
but no separate command/status receipts. Target and client records and logs
were independently checked. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-gates-semiring-sharing-evidence/BUNDLE.json).

The object-code inversion sharing `8fa57453aa` removes 15 net lines,
bringing the reviewed series to 8574. Paired targets and the direct
ObjectCodeSeal client pass; all 83 existing declaration types and axiom
reports, and 15 forced equation declarations, match. ObjectCodeClosure is a
precompiled input without a matching source/object receipt, and package and
other transitive inputs remain cached. Interface probes have matching logs but
no separate command/status receipts; early failed probe outputs were
overwritten. Target and client records and logs were independently checked.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-object-code-bound-evidence/BUNDLE.json).

The object expression evaluation sharing `b060afcaaf` removes eight net
lines, bringing the reviewed series to 8582. Paired targets and the direct
ObjectPolynomial client pass; all 36 existing declaration types and axiom
reports, and 11 materialized equation theorems, match. ObjectMultiplication
is a precompiled direct input without a matched receipt; an earlier
NaturalExpression receipt matches its source but a different object. Other
transitive inputs remain cached. Interface and equation probes have matching
logs but no separate command/status receipts. The target/client records and
interface logs were independently checked; the separate equation comparison
was performed by the prototype author. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-object-expression-sharing-evidence/BUNDLE.json).

The bounded construction sharing `1b2d29dded` removes 91 net lines,
bringing the reviewed series to 8673. Both Assembly and Bound targets and the
CurrentConstruction production client pass in paired pinned replays. All 56
existing declaration, equation and axiom reports match, including five forced
equations; the sole new bounded helper uses the standard three axioms. The
current-source refresh rebuilt 93 local prerequisites, authenticated 12 peer
and 76 borrowed objects, and corrected a superseded mask/RankForcing input.
Each replay pins 182 non-target local source/object pairs and 73 direct
external objects before and after; transitive external dependencies remain
precompiled. Ninety refresh warnings and 11 peer warnings lack paired
preparation baselines; 22 generated-auxiliary probe warnings match. Assembly
now imports BoundPell and exposes the formerly Bound-only declarations earlier.
Earlier missing-object failures and stale-Fol preliminary results are retained.
Independent graph, proof and pinned-replay reviews pass. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261028-construction-sharing-evidence/BUNDLE.json).

The Boolean rotation proof reuse `d19aea45fd` removes 16 net lines,
bringing the reviewed series to 8689. Paired targets and both direct clients
pass; all six surviving declaration types and axiom reports match. The one
removed autogenerated proof auxiliary has no tracked source references and is
not registered in the baseline default simp set. All nine local target
prerequisites match earlier receipts. Foundation Matrix co-import fails in both
orders in both phases because of an existing naming collision; other client
inputs and external dependencies remain precompiled. The eight build records,
logs and target pins were independently checked. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-boolean-rotation-sharing-evidence/BUNDLE.json).

The positive Pell norm conversion sharing `d68db620ea` removes ten net
lines, bringing the reviewed series to 8699. Both phases rebuild the 19
affected modules and the CurrentConstruction production client; all 42 old
namespace declarations, four forced equations and four private declarations
have matching type and axiom reports. The shared helper retains the `0 < f`
guard and uses the standard three axioms. Source/object pins cover 184 local
modules and 73 direct external inputs; unaffected local and transitive external
objects remain precompiled. Fourteen MF/local-normalization prerequisites were
rebuilt after a concurrent documentation update; three preparation warnings
lack paired baselines. Twelve Pell and 22 construction generated-name warnings
match per phase. The interrupted first attempt and overwritten timing files are
documented. Independent graph and receipt reviews pass. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-pell-norm-sharing-evidence/BUNDLE.json).

The low-mask support sharing `73fcfa082e` removes ten net lines, bringing
the reviewed series to 8709. Paired targets and three representative clients
pass; all 126 surviving public/generated and three private declaration reports,
plus 16 materialized equation reports, match. Fourteen autogenerated names
disappear; no tracked references or baseline default simp registrations were
found. Of 68 unchanged local selected objects, 41 match recent receipts; 27
historical Diophantine objects and external package dependencies remain
precompiled. Four matching target/client warnings differ only by source line
number; independent simp and private probes lack separate command receipts.
Initial missing-object and root-path failures are retained. Independent review
passes. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-mask-support-sharing-evidence/BUNDLE.json).

The physical tile row proof reuse `6439fb5228` removes 59 net lines,
bringing the reviewed series to 8768. Paired targets and the direct
PhysicalOrder client pass; 61 data equalities hold by `rfl`, and 248 retained
or materialized declaration type and axiom reports match, including 61 data
equations. Two autogenerated simp auxiliaries disappear; no tracked source
references or default simp registrations were found. Nine local target
prerequisites match prior receipts, while six BusyBeaver objects are shared
precompiled inputs without matching object receipts. Foundation Matrix
co-import fails in both phases due to an existing collision; transitive
package inputs remain precompiled. Initial path failures are retained, and an
early audit traceback was not saved. Independent review passes. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-physical-row-sharing-evidence/BUNDLE.json).

The physical tile order proof reuse `cc69e80ca0` removes 37 net lines,
bringing the reviewed series to 8805. Paired targets, the existing check and
CurrentKernelResidues client pass; 34 surviving namespace declaration reports
and eight forced equation reports match. Three autogenerated proof auxiliaries
disappear without tracked references or baseline default simp registrations.
Ten DiophantineConsistency prerequisites match receipts; six BusyBeaver objects
remain unmatched precompiled inputs, and external packages remain precompiled.
Foundation Matrix co-import fails identically in both phases due to the existing
collision. Fourteen build and probe records, local source/object hashes and
matching logs were independently checked. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-physical-order-sharing-evidence/BUNDLE.json).

The local cell construction proof reuse `b616cba766` removes 78 net
lines, bringing the reviewed series to 8883. Paired targets, the direct
CurrentWordConstruction client and existing checks pass; 40 surviving
declaration reports and five forced equations match. One unused private helper
and 45 compiler-generated auxiliaries disappear; no tracked qualified
references or baseline default simp registrations were found. Of 133 selected
local source/object pairs, 33 were rebuilt, 73 match prior pins and 27
historical Diophantine objects remain unmatched precompiled inputs. Two
preparation warnings lack a paired baseline; Foundation Matrix co-import fails
in both phases due to an existing collision. Independent graph and 46-record
receipt audits pass. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-local-cell-sharing-evidence/BUNDLE.json).

The radix digit proof reuse `114e39f96f` removes 14 net lines, bringing
the reviewed series to 8897. Paired targets and the NativeVariableMask client
pass; all 16 existing namespace declaration reports and two forced equations
match. Compatibility probes check definitional equality of the word functions
and use of periodic_sum without a NeZero instance. Of 59 unchanged selected
local objects, 29 match recent receipts and 30 historical Diophantine objects
remain unmatched precompiled inputs. Foundation Matrix co-import fails in both
phases due to the existing collision; compatibility probes lack separate
command/timing receipts. Twelve build and interface records and 62 local
source/object pins were independently checked. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-radix-digits-sharing-evidence/BUNDLE.json).

The word top-bound proof reuse `b4c6cf72f0` removes 122 net lines,
bringing the reviewed series to 9019. Paired targets, maintained checks and
the CurrentWordScalarWitness production client pass; all 16 old theorem
reports and 46 client namespace declarations match. The private Facts bridge
preserves all six fields and the original NeZero premise. Twenty-seven
autogenerated proof/simp names disappear without tracked references or
default simp registrations. The pinned replay checks 148 local and 65 direct
external objects per phase; 27 historical local objects and transitive package
inputs remain precompiled. The import set gains nine MF modules, and Foundation
Matrix co-import already fails in both phases. The maintained checks emit one
matching exponentiation warning per phase. Independent graph, source, receipt
and declaration reviews pass. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-word-top-sharing-evidence/BUNDLE.json).

The finite two-row proof simplification `c44ea5ddf0` removes 18 net
lines, bringing the reviewed series to 9037. Paired targets and focused
clients pass; all 46 old public and private declaration reports and all 11
materialized definition equations match. Three new generated simp auxiliaries
use only propext and are not registered as default simp rules. The 87-node
local graph has 67 rebuilt nodes, three pinned FirstOrder inputs and 17
unaffected precompiled local objects; transitive external dependencies remain
precompiled. Five ArithmeticDAGSemantics preparation warnings lack a paired
baseline; earlier simpa warnings and an initial lazy-equation probe failure
are retained. Independent graph, 82-record and equation audits pass. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-fin-two-rows-evidence/BUNDLE.json).

The carry construction proof reuse `3a900e9364` removes 28 net lines,
bringing the reviewed series to 9065. Paired targets and five direct clients
pass, including MF copies after its three prerequisites were rebuilt against
matching inputs. All 18 surviving ordinary declaration type/axiom reports and
the forced raw equation match. One autogenerated proof auxiliary disappears
without tracked references or baseline default simp registration. The full
client graph has 152 local nodes and 65 direct external imports; 27 historical
local inputs and transitive packages remain precompiled. The import set gains
six MF modules and both Foundation Matrix import orders already fail in both
phases. Initial client/input and audit setup failures are retained. Independent
source, graph, input and receipt audits pass. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-carry-sharing-evidence/BUNDLE.json).

The word-copy proof reuse `f9fd7daf20` removes 58 net lines, bringing
the reviewed series to 9123. Paired targets, maintained checks and the direct
CurrentWordOrigin client pass; all 15 retained declaration reports and the
forced constructedWord equation match. Explicit three-field MarkedWord and
six-field Facts bridges preserve the original guards, and compatibility probes
cover zero N without a NeZero instance. Sixteen generated proof auxiliaries
disappear without tracked references or baseline default simp registrations.
The pinned replay checks 160 non-target local and 65 direct external inputs;
27 historical local objects and transitive package inputs remain precompiled.
The original graph omitted one carry-to-MF import edge; the corrected graph has
the same node set and topological build order, and both records are retained.
Ordinary Foundation Matrix co-import fails identically in both phases. Independent
graph, input, bridge and receipt audits pass. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-word-copies-sharing-evidence/BUNDLE.json).

The kernel residue proof reuse `40daf05518` removes 52 net lines,
bringing the reviewed series to 9175. Paired targets, the maintained check
and CurrentControllerUnits client pass; 35 surviving public/generated reports,
seven surviving private reports and five forced equations match. Seven unused
private helpers and their generated names, plus four public generated
auxiliaries, disappear without tracked full-name references or default simp
registrations; two private evaluator bridges are added. Seven prerequisites
were rebuilt, and each replay pins 99 local and 66 direct external inputs.
Historical local objects and transitive external packages remain precompiled.
The controller client has one matching exponentiation warning per phase;
interface probes have eight matching generated-name warnings. Foundation Matrix
co-import already fails in both phases. A separate reviewer from the source
prototype independently reconstructed the graph and checked the refresh and
receipts. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-kernel-residues-sharing-evidence/BUNDLE.json).

The word-padding proof reuse `7fe52ac4b0` removes 86 net lines, bringing
the reviewed series to 9261. Paired targets, maintained checks and the direct
CurrentWordHighMask client pass; all 11 old public declaration reports match.
The six-field Facts bridge was checked in both directions, and the original
ordinary existential witness construction remains. Thirteen autogenerated
namespace names and four unused private definitions/theorems with eight
associated private auxiliaries disappear without tracked qualified references
or default simp registrations. Twelve pinned runs check 163 local and 65 direct
external inputs; 27 historical local objects and transitive packages remain
precompiled. Both Foundation Matrix import orders already fail in both phases.
Final logs are warning-free; earlier failed and interrupted attempts are
retained. Independent graph, receipt, bridge and removal audits pass. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-word-padding-sharing-evidence/BUNDLE.json).

The word-clause proof reuse `7289054dfc` removes 41 net lines, bringing
the reviewed series to 9302. Paired targets, maintained checks and downstream
TopBounds checks pass; all 13 retained declaration reports and the forced
displacement equation match. The six-field Facts bridge retains the original
assumptions, and compatibility probes cover zero N without NeZero. Four
autogenerated proof auxiliaries disappear without tracked references or default
simp registrations. Twelve pinned runs check 144 unchanged local source/object
pairs and 65 direct external objects; 27 historical HTP and transitive external
objects remain precompiled. TopBoundsChecks emits one matching exponentiation
warning per phase; ordinary Foundation Matrix co-import fails identically in
both orders. Initial bad-namespace and audit-script failures are retained, as
is the original precommit graph. Independent graph, receipt and interface audits
pass. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-word-clause-sharing-evidence/BUNDLE.json).

The word-origin proof reuse `3fedbfa61b` removes 39 net lines, bringing
the reviewed series to 9341. Paired targets, maintained checks and the direct
HighMask client pass; six old theorem reports match. Two private bridges copy
all three MarkedWord and six Facts fields, with two-way compatibility and
constructedWord definitional equality checked. Eight autogenerated proof names
disappear without tracked qualified references or default simp registrations.
Eight pinned replays check 164 non-target local and 65 direct external inputs;
27 historical HTP objects and transitive external packages remain precompiled.
Ordinary Foundation Matrix co-import fails identically in both phases; MF
co-import succeeds. Independent graph, receipt, bridge and removal reviews pass.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-word-origin-sharing-evidence/BUNDLE.json).

The word high-mask proof reuse `ee22e984d8` removes 24 net lines,
bringing the reviewed series to 9365. Paired targets, maintained checks and
the CurrentDummyMutation client pass; six old theorem reports match. Two
private bridges preserve the three MarkedWord and six Facts fields, checked in
both directions. Eight generated proof auxiliaries disappear without tracked
qualified references or default simp registrations. Twelve pinned runs check
167 non-target local and 65 direct external inputs; 27 historical local objects
and transitive external packages remain precompiled. Ordinary Foundation Matrix
co-import fails identically in both phases; MF co-import succeeds in the tested
order. Independent graph, input, bridge and receipt audits pass. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-high-mask-sharing-evidence/BUNDLE.json).

The bounded AX witness sharing `6ab638f6e4` removes 24 net lines,
bringing the reviewed series to 9389. The prior bounded-enumerator source was
co-authored by Claude (commit `9168659697`); this refactor shares its exact
witness argument with the lower preservation layer. Paired current-source
targets and runtime clients pass, and the ten-witness list and bound are
unchanged by `rfl`. Named theorem statements and the other common declaration
reports match, but the surviving autogenerated `axWitnesses_le._simp_7`
changes type; three generated auxiliaries disappear and three others are
added. None of these changed generated names is a default simp rule or has a
tracked Lean reference. Forty-two prerequisites were rebuilt; 35 seeds have
matching direct-input receipts and 66 unaffected local objects remain pinned
historical inputs. External transitive packages remain precompiled. Each
expanded interface probe emits 170 generated-name warnings; target/client logs
are warning-free. Initial probe failures and the limited scope of the broader
reference search are retained. Independent graph, witness and receipt audits
pass. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-claude-ax-sharing-evidence/BUNDLE.json).

The exact packing transport sharing `9aee4917b7` removes 25 net lines,
bringing the reviewed series to 9414. Its original Packing and Variation
proofs were in Claude-coauthored commits `5fcd5632b3` and `16bbf50270`.
The earlier exact identity is now proved in Packing and also yields the
modular residue; both old theorem statements remain. Paired Packing, Variation,
PackingCells and actual Assembly builds pass; 67 old target declaration reports
and all 39 materialized Assembly/Bound declaration reports match, together with
their forced equations. Two named theorems and one generated congruence name
are added; the new generated name is not a default simp rule. Six Assembly
dependencies were rebuilt, 20 reused with matching direct-input receipts, and
each phase pins 111 local and 43 direct external inputs. Historical local and
transitive package objects remain precompiled. Packing emits five and
PackingCells four matching warnings per phase; one shared preparation warning
lacks a paired baseline. Initial failed prototypes and an incomplete audit
observation are retained. Independent proof, graph and receipt reviews pass.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-claude-transport-sharing-evidence/BUNDLE.json).

The symbolic oracle dispatch sharing `86c4490d08` removes 24 net lines,
bringing the reviewed series to 9438. The bounded module originated in the
Claude-coauthored commit `11f7ea173b`. A relation-parametric proof now serves
both versions while preserving the branch guards, positive-spare hypothesis
and exact `boxW` bound. Paired target and client builds pass, as do comparisons
of 160 stable declaration type and axiom reports and default simp membership.
One unstable generated proof auxiliary was renamed. Cached upstream inputs and
external libraries remain precompiled; direct-input hashes were sampled after
the builds. An invalid initial interface receipt is retained, with fresh stable
reruns replacing it. Independent proof review confirms the branch conditions
and bound. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-oracle-sharing-evidence/BUNDLE.json).

The bounded DAG transfer and copy sharing `ba484e92b4` removes 35 net lines,
bringing the reviewed series to 9473. The original macro module was introduced
in the Claude-coauthored commit `ca0c31b62d`. Private general lemmas now
share the 17 loop proofs, preserving each node and register check, size bound
and tower clock. Paired builds from Macros A through DAG Halt pass, and all
67 target-namespace declaration type and axiom reports match, including
generated auxiliaries; the two Halt objects are identical. Forcing equations
also reveals two new private helpers and 22 private matcher declarations.
Independent whole-environment simp and instance censuses match. The builds use
precompiled upstream dependencies, though direct imports were hashed before
and after compilation. The initial failed setup's compiler log was overwritten;
its reconstructed transcript is excluded from the successful evidence. See
[the evidence bundle](../../reviews/lean-proof-simplification-20261028-dag-macro-sharing-evidence/BUNDLE.json).

The positive-shift sharing `0b19c1af58` removes 33 net lines, bringing the
reviewed series to 9506. The arithmetic sentence proof originated in the
Claude-coauthored commit `e7dc22a493`. Three existing declarations move
verbatim to their already-imported syntax owner, preserving their qualified
names and exposing them earlier; both arithmetic proofs now reuse the same
shift equivalence. Forty-eight paired-lane source builds pass, including the
construction, window, object-equation and HA-stability clients. Existing
type and axiom reports and the 33,211 checked simp entries match; three new
generated `PositiveZero._proof` names appear. Three cached direct object
prerequisites lack matching source/object receipts, and not all 36 reverse
clients were replayed. Earlier mixed-provider and missing-Pell attempts are
retained but excluded. Object and arithmetic imports are checked separately:
their combined import encounters the same existing Matrix conflict in both
phases. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-positive-shift-sharing-evidence/BUNDLE.json).

The controller dummy-map proof `61482d12ea` removes 26 net lines, bringing the
reviewed series to 9532. Its original module was introduced in the
Claude-coauthored commit `172621966a`. The proof now relates the decoded
coordinate directly to its position and splits on whether that position is
selected. Paired controller, variation and assembly builds pass; all 41 target
declaration type and axiom reports and the 38,804-entry global simp set match.
Thirty direct-input occurrences match same-phase outputs or prior
current-source/object receipts; transitive dependencies remain precompiled.
The failed initial proof and a wrong-namespace probe are retained but excluded,
and the original failed proof source was reconstructed after being overwritten.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-controller-dmap-evidence/BUNDLE.json).

The repeated Cantor square-bound simplification `34bb4f5483` removes six net
lines, bringing the reviewed series to 9538. Both affected modules originated
in Claude-coauthored commits `9168659697` and `d9775aa0f5`. The original ring
identity and inequalities now compose directly. Paired builds of both targets
and their clients pass; 106 public and 20 private declaration type and axiom
reports, forced equations and namespace-scoped simp entries match. Six cached
direct input source/object pairs match prior receipts; transitive dependencies
remain precompiled. Two failed interface probes are retained, but their
generated sources were overwritten. An initial `nlinarith` probe had missing
imports and proves no mathematical limitation. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-cantor-bound-evidence/BUNDLE.json).

The scheduler proof sharing `82ac343059` removes a duplicate induction and
scheduling argument while adding two net source lines for preserved wrappers;
the reviewed series therefore stands at 9536 net lines removed. The bounded
module originated in the Claude-coauthored commit `9168659697`. The original
bounded clock estimates and hypotheses remain, and the unbounded results now
discard those bounds. Paired builds and refreshed production clients pass;
all 37 old target declaration reports and namespace-scoped simp entries match.
Two new bounded helper names are visible earlier. Two unchanged-source client
objects differ by bytes, although their checked declaration reports match.
Transitive inputs remain precompiled; the first superseded interface probe was
overwritten and is excluded. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-enum-fair-sharing-evidence/BUNDLE.json).

The generated kernel port-bound sharing `5093f59cd6` removes 11 net Lean
lines, bringing the reviewed series to 9547; the accompanying generator edits
make the four-file total a three-line reduction. Gap's three coefficient
bounds now reuse the same Split estimate instead of copying its proof. Both
generators reproduce their outputs, with coefficient and position data
unchanged. Paired coherent kernel builds and wrapper checks pass after
rebuilding a stale SelectiveCarry dependency chain. All 81 common public
declaration reports, 55,118 global simp entries and 23,324 instances match.
One public alias is added; Gap's private helper and five generated auxiliaries
are removed. The earlier stale-cache client failure is retained and excluded,
and other transitive providers remain precompiled. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-generated-box-sharing-evidence/BUNDLE.json).

The bounded DAG unpair sharing `f3faf5c4b3` removes 37 net Lean lines,
bringing the reviewed series to 9584. Its original module came from the
Claude-coauthored commit `ca0c31b62d`. One private walk now handles the two
registers, preserving their nodes, updates and `tower j (L+13)` bound. Paired
current-provider builds through DAG Halt pass, and five unchanged-source
clients have identical objects. The 116 common public declaration reports
and 29,279 global simp entries match. Thirteen unstable generated loop proof
names disappear and sixteen private helper/auxiliary names are added; none is
a default simp rule. The failed initial draft and name probe are retained,
and other transitive dependencies remain cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-dag-unpair-sharing-evidence/BUNDLE.json).

The seam-colour proof sharing `fa98fc9b83` removes 14 net Lean lines,
bringing the reviewed series to 9598. Its original module came from the
Claude-coauthored commit `3cd04ac37f`. A single four-case fact now supplies
both north and south seam colours. Paired target, tiling and construction
builds pass over refreshed providers; 61 target declaration reports and
29,730 global simp entries match. The changed-byte tiling client has matching
reports for its 18 checked declarations. Three local target timing pairs show
a median user-CPU increase from 29.71 to 31.10 seconds; this is not a general
benchmark. Earlier old-provider endpoint attempts and a failed simplifier are
retained but excluded, and transitive dependencies remain cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-seam-sharing-evidence/BUNDLE.json).

The site edge-check sharing `6e40d24f7c` removes 14 net Lean lines, bringing
the reviewed series to 9612. The bounded tape module originated in the
Claude-coauthored commit `11f7ea173b`. Two identical edge-check proofs now
come from the existing site module. Paired site, frame, tape-control and
tape-run builds pass; 73 common public/generated reports, five surviving
private reports, the bounded endpoint and 29,339 global simp entries match.
Two helper names become public, eight private names disappear and five
public/generated names appear. Fresh probes pin direct inputs; broader
reference searches were terminated, so the no-reference check is limited to
the project Lean tree. Other transitive dependencies remain cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-site-check-sharing-evidence/BUNDLE.json).

The generated near-target isolation sharing `53d3f3ff97` removes 13 net
Lean lines, bringing the reviewed series to 9625. One bounded-offset argument
now serves the linear and quadratic cross-target proofs in both geometries;
the generator emits the shared lemma and the numeric data is unchanged.
Paired geometry, certificate, source, adopted kernel and wrapper builds pass,
as does independent regeneration. The 157 common public reports, 31,715
global simp entries and 13,981 instance entries match. A public helper and two
generated auxiliaries appear; four public and two private generated proof
names disappear. Preliminary overwritten or failed attempts are retained as
historical evidence, and transitive providers remain cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-near-isolation-sharing-evidence/BUNDLE.json).

The bounded tape-return sharing `c6960dfa9a` removes a duplicate induction
and one net Lean line, bringing the reviewed series to 9626. The source was
introduced in Claude-coauthored commit `11f7ea173b`. The nonempty case now
uses the existing stronger return theorem with the same `fileCost` bound; the
empty case remains reflexive. Paired target and clients through the tape-run
endpoint pass. The 38 target names, 24 public type/axiom reports, 29,189 global
simp entries and bounded endpoint reports match. Two initial malformed-overlay
attempts are excluded, and transitive providers remain cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-tape-return-sharing-evidence/BUNDLE.json).

The tiling row relation simplification `8ee624a4d0` removes 47 net Lean lines,
bringing the reviewed series to 9673. Its original module came from the
Claude-coauthored commit `3cd04ac37f`. The existing halt, head and receiver
guards now drive one direct case analysis. Three paired target builds and four
paired tiling/construction clients pass. All 59 old declaration reports and
29,730 global simp entries match; two new generated auxiliaries are not default
simp rules. Paired timing samples show no substantial local regression, but
are not a controlled benchmark. Superseded and failed tactics are retained,
and transitive providers remain cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-rowrel-sharing-evidence/BUNDLE.json).

The mask membership cast simplification `06cf327bb2` removes eight net Lean
lines, bringing the reviewed series to 9681. Its original module was in the
Claude-coauthored commit `5fcd5632b3`. Cast normalization now proves the
unchanged predicate equivalence directly. Paired mask, rank, window and
refreshed construction endpoint builds pass; all 37 target names, 32 public
and five private type/axiom reports and 35,447 global simp entries match.
The separate construction supplement completes the checks initially marked
pending. Historical source-sample exceptions and failed probes are recorded;
transitive providers remain cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-mask-cast-evidence/BUNDLE.json).

The generated native row padding sharing `2f04c5dcb3` removes 76 net Lean
lines, bringing the reviewed series to 9757; the accompanying generator edit
makes the two-file total a 72-line reduction. A private padded-coordinate fact
replaces repeated per-row facts in 22 proofs without changing row data.
Regeneration and paired current-provider target/client builds pass, and both
client objects match baseline. The 100 public and 22 old private declaration
reports, 31,715 global simp entries and 13,981 instances match; three private
names are added. One paired repeat used 35.28s baseline versus 36.94s final
user CPU, a small local sample. The slower v1 and Lean-internal v2 are retained
as superseded; transitive providers remain cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-native-row-sharing-evidence/BUNDLE.json).

The selective coefficient sharing `dcba8839c3` removes 14 net Lean lines,
bringing the reviewed series to 9771. It reuses the exact-coefficient theorem
in the occupied branch. The target and three direct clients pass paired builds,
with identical client objects; all 11 target type/axiom reports, 55,118 global
simp entries and 23,324 instances match. Direct providers match prior
source/object receipts, while transitive dependencies remain cached. Failed
setup and interrupted probes and the limitations of timing are recorded in
[the evidence bundle](../../reviews/lean-proof-simplification-20261028-coefficient-sharing-evidence/BUNDLE.json).

The bounded DAG branch sharing `74e80544e2` removes nine net Lean lines,
bringing the reviewed series to 9780. The original module was introduced in
Claude-coauthored commit `3b818a8127`. Two private helpers factor the repeated
node occurrence decompositions while preserving the eight exit and clock
statements. Paired target and two direct clients pass, with identical client
objects; all 35 existing declaration reports and 29,223 global simp entries
match. A sequential target repeat used 29.12s versus 29.17s user CPU under
shared load. Two private helper names are added, and transitive inputs remain
cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-dag-run-sharing-evidence/BUNDLE.json).

The cell-support cast normalization `97a7679281` removes eight net Lean
lines, bringing the reviewed series to 9788. The original module was added in
Claude-coauthored commit `f79467f544`. After refreshing an outdated CellLocal
provider, paired target and decoding-client builds pass, with identical client
objects; all 59 existing declaration reports and 33,296 global simp entries
match. One generated public auxiliary is added without global simp registration.
Direct project providers match prior source/object receipts; the transitive
closure remains cached. The initial stale-provider run and corrected overlay
setup are described in [the evidence bundle](../../reviews/lean-proof-simplification-20261028-support-cast-evidence/BUNDLE.json).

The origin block addition sharing `526cb2490b` removes six net Lean lines,
bringing the reviewed series to 9794. The original module was introduced in
Claude-coauthored commit `5fcd5632b3`. The proof now uses block addition and
the one-block representation of the origin indicator, without a separate
induction. Paired target and both direct-client builds pass with identical
client objects; all 33 target declaration reports and 29,064 global simp
entries match. Direct project inputs match prior source/object receipts; the
transitive dependency closure remains cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-origin-block-evidence/BUNDLE.json).

The Pell reflection simplification `3b3572a2d6` removes eight net Lean
lines, bringing the reviewed series to 9802. Both reflection forms now follow
from their additive identities by reassociation and guarded subtraction
cancellation. Paired targets and refreshed HalfIndex clients pass with
identical client objects; all 26 old declaration reports, 28,968 global simp
entries and 13,167 instances match. Two generated public auxiliaries are
added without global registration. An earlier client replay used a stale
provider and is superseded; the wider transitive closure remains cached. See
[the evidence bundle](../../reviews/lean-proof-simplification-20261028-pell-reflection-evidence/BUNDLE.json).

The Pell norm balance sharing `4b7de916da` removes four net Lean lines,
bringing the reviewed series to 9806. A subtraction-free identity replaces
duplicated polynomial decompositions in norm preservation and its converse.
Paired targets, four direct clients and both combined seven-module chains
through HalfIndex pass with pinned project inputs. All 78 old target reports
and 38 endpoint declaration reports and both global registration censuses
match; some compiled client objects differ. One public balance theorem is
added. External and further transitive providers remain cached; see [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-pell-balance-evidence/BUNDLE.json).

The modular-offset cancellation `9c55a5db20` removes 22 net Lean lines,
bringing the reviewed series to 9828. The original module was introduced in
Claude-coauthored commit `f79467f544`. Adding the offset's modular complement
replaces the quotient comparison and case analysis. Paired target and decoding
client builds pass with identical client objects; all 60 target declaration
reports and 33,296 global simp entries match. Direct project providers match
current-source receipts; the transitive closure remains cached. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261028-cell-mod-cancel-evidence/BUNDLE.json).

The half-binomial divisor cancellation `00971db686` removes four net Lean
lines, bringing the reviewed series to 9832. The module was introduced in
Claude-coauthored commit `90f67cbdd9`. Existing zero-remainder and modular
removal lemmas replace the manual quotient comparison in a private proof.
Paired target and two direct-client builds pass with identical client objects;
all seven target declaration reports and 29,056 global simp entries match.
Direct project providers match prior current-source receipts; the transitive
closure remains cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-halfbinom-cancel-evidence/BUNDLE.json).

The initial-machine-step sharing `1518cb44ce` removes eight net Lean lines,
bringing the reviewed series to 9840. Wang soundness was introduced in
Claude-coauthored commit `64422b55f4`. The initial action and first step are
proved once and reused by both existing downstream theorems. Paired builds and
a TilingTable client pass; 148 existing co-import and 73 client declaration
reports, 29,730 simp entries and 13,383 instances match, though client objects
differ. Two public helpers and one generated auxiliary are added; co-import
short names were checked within the documented scope. Transitive providers
remain cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-wang-initial-sharing-evidence/BUNDLE.json).

The bounded row-witness sharing `fc85f9a87d` removes 11 net Lean lines,
bringing the reviewed series to 9851. Existing binary and unary constructors
replace repeated tag-specific witnesses, retaining all tag and lookup guards.
Paired target and two clients pass with identical client objects against a
refreshed nearby provider chain; all 60 declaration reports, 25,317 simp
entries and 11,807 instances match. The slower initial tactic variant was
superseded. The changed branch bodies predate a Claude-coauthored adjacent edit;
the remaining transitive closure is cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-annotated-bound-witness-evidence/BUNDLE.json).

The controller stride reuse `61116bd1db` removes nine net Lean lines,
bringing the reviewed series to 9860. Git blame attributes the replaced proof
to Claude-coauthored commit `172621966a2d`. Existing quotient and periodicity
lemmas replace a contradiction and a power-witness calculation. Paired target
and direct Controller builds pass with identical client objects; target
reports, 38,766 simp entries and 16,545 instances match. Direct providers
match current-source receipts, with a historical workspace-source sampling
exception recorded; the broader closure remains cached. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261028-controller-stride-period-evidence/BUNDLE.json).

The safe suffix sharing `5e81225d7d` removes two net Lean lines, bringing
the reviewed series to 9862. The original proof was introduced in
Claude-coauthored commit `16bbf502706`. A shared suffix-zero invariant replaces
two repeated contradictions while retaining both safety guards. Paired target
and Assembly builds pass with identical client objects; all six target reports,
38,804 simp entries and 16,567 instances match. The refreshed target pair used
58.88s baseline and 32.11s final user CPU under shared load. Current block,
controller and Wang-plane providers were refreshed; older Pell, HalfBinomial
and tiling objects remain cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-variation-tail-sharing-evidence/BUNDLE.json).

The bounded DAG linear estimate sharing `934bd5397f` removes six net Lean
lines, bringing the reviewed series to 9868. The replaced proof came from
Claude-coauthored commit `ca0c31b62d5`. The plus-one bound now instantiates the
existing general bound, which is visible one module earlier. Paired macro and
RootA builds pass with identical checked client objects; existing B-boundary
declaration reports and global simp/instance censuses match. Direct inputs
match current-source receipts; the transitive closure remains cached. See
[the evidence bundle](../../reviews/lean-proof-simplification-20261028-dag-linear-bound-evidence/BUNDLE.json).

The odd-factor exponent sharing `4c1dbc5ea9` removes seven net Lean lines,
bringing the reviewed series to 9875. The module originated in Claude-coauthored
commit `90f67cbdd9`. A private comparison replaces duplicated arguments in
exponent uniqueness and the binomial valuation bound. Paired target and three
clients pass with identical client objects; all 11 existing target reports,
29,039 simp entries and 13,232 instances match. One private helper is added;
direct providers match current-source receipts and the wider closure remains
cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-binom-odd-sharing-evidence/BUNDLE.json).

The packing-to-positive-zero sharing `c54276ca56` removes six net Lean
lines, bringing the reviewed series to 9881. An actual packing now supplies
both the inconsistency and blank-halting endpoints through one shared theorem.
Paired targets and check clients pass over a refreshed carrier/seed/provider
chain, with identical client objects; existing named endpoint reports, 55,579
simp entries and 23,485 instances match. One public helper and its generated
proof are added; two unregistered generated endpoint proofs disappear. An
older SignedPellResidue object and the wider transitive closure remain cached.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-packing-positive-sharing-evidence/BUNDLE.json).

The window remainder bound `94638c37e5` removes four net Lean lines, bringing
the reviewed series to 9885. Its original proof was introduced in
Claude-coauthored commit `d2a666efce`. A direct strict-to-weak inequality
replaces the contradiction while preserving the modulus and bound. Paired
target and WindowZero builds pass with identical client objects; all 43 target
reports, 35,447 simp entries and 15,617 instances match. The other direct
client was not rebuilt and older project objects remain in the cached
transitive closure. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-window-rem-bound-evidence/BUNDLE.json).

The input-tile impossible-case sharing `ffe53fb10a` removes 12 net Lean
lines, bringing the reviewed series to 9897. Three input classifications
share the discharge of impossible constructors while retaining each substantive
case. Paired target, Signals and maintained check builds pass with identical
client objects; all 37 named/generated declaration reports, 55,111 simp entries
and 23,348 instances match. Earlier variants were superseded; the direct
provider matches a source/object receipt and the wider closure remains cached.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-wang-input-cases-evidence/BUNDLE.json).

The modular cancellation sharing `0d0b625be5` replaces three independent
model-arithmetic arguments with one qualified helper and leaves the reviewed
net line reduction at 9897: its four-file diff has 33 insertions and 33
deletions. All three targets and their ControllerData, CellDecoding and
PellHalfIndex clients pass paired builds. All 241 existing names, 231 public
reports, private reports, 38,882 simp entries and 16,587 instances match;
client object hashes differ after the added imports. The new helper is not a
global simp lemma or instance. Direct providers match current-source receipts;
the broader closure remains cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-shared-modular-cancel-evidence/BUNDLE.json).

The generated kernel range projection sharing `784c1c2775` removes 48 net
Lean lines, bringing the reviewed series to 9945; its generator edits remove
16 additional lines. Six generated proofs pass the existing conjunction
projections directly to `nlinarith`. Both generator replays and paired targets
and wrappers pass; all 88 target and 36 wrapper declaration reports, 55,118
simp entries and 23,324 instances match, though object hashes differ. An older
SelectiveCoefficientBounds object remains in the cached transitive closure;
prior old/current-provider builds of its PolynomialRangeBounds client produced
identical objects. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-kernel-range-projections-evidence/BUNDLE.json).

The low-mask residue simplification `92cfb70d2d` removes six net Lean
lines, bringing the reviewed series to 9951. The affected proof is attributed
to Claude-coauthored commit `f4920e87b3e`. Modular laws replace quotient
reconstruction. Paired target and Assembly builds pass with identical client
objects; all five target reports, 35,447 simp entries and 15,616 instances
match. Direct providers match receipts; older ControllerLift, HalfBinomial,
Legendre and Pell objects remain cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-rank-mask-residue-evidence/BUNDLE.json).

The one-term binomial sum sharing `a5beca5e0f` removes five net Lean lines,
bringing the reviewed series to 9956. The affected proof originated in
Claude-coauthored commit `90f67cbdd9`. One private base-case lemma replaces two
repeated arguments. Paired target and HalfBinomial builds pass with identical
client objects; all 40 existing target reports, 29,034 simp entries and 13,227
instances match. One private helper is added; the wider closure remains cached.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-binom-expansion-zero-evidence/BUNDLE.json).

The positive sphere equivalence simplification `6f53b13909` removes 14 net
Lean lines, bringing the reviewed series to 9970. Pointwise equivalences are
lifted through the same positive witness rather than reconstructed separately
in both directions. Paired target and check builds pass with identical client
objects; all 46 declaration reports, 55,579 simp entries and 23,485 instances
match. A restored docstring is retained; older SignedPellResidue and other
transitive objects remain cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261028-nonzero-sphere-sharing-evidence/BUNDLE.json).

The binary formula-code uniqueness sharing `3148a695af` removes four net
Lean lines, bringing the reviewed series to 9974. One private lemma handles the
same inversion and child uniqueness argument for all three binary tags. Paired
target and ObjectCodeSeal builds pass with identical client objects; all 88
existing declaration reports, 12,375 simp entries and 5,184 instances match.
One private helper is added; the broader closure remains cached. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261029-object-binary-unique-evidence/BUNDLE.json).

The DAG zero-register skip `4e897bac04` removes two net Lean lines, bringing
the reviewed series to 9976. The affected proof was introduced in
Claude-coauthored commit `ca0c31b62d5`. The empty clear uses the existing
zero-test and skip rules directly with the original guard and clock bound.
Paired RootA/B/C builds pass with identical client objects; all 324 checked
names, 294 public/generated reports, private reports, 29,279 simp entries and
13,370 instances match. Direct providers are source-pinned and the wider
closure remains cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-dag-zero-skip-evidence/BUNDLE.json).

The binary carry boundary simplification `a3af2f89c7` removes four net Lean
lines, bringing the reviewed series to 9980. The affected proof originated in
Claude-coauthored commit `5fcd5632b3`. The proof shares its out-of-range bound
and uses nonnegative inequalities for the zero-sum case. Paired target,
RankForcing and Saturation builds pass with identical client objects; all 14
declaration reports, 28,971 simp entries and 13,167 instances match. Another
direct client, WindowDigits, was not rebuilt; the wider closure is cached. See
[the evidence bundle](../../reviews/lean-proof-simplification-20261029-binary-carry-evidence/BUNDLE.json).

The carrier positive-zero equivalence sharing `2ad82db137` removes seven net
Lean lines, bringing the reviewed series to 9987. Existing pointwise
equivalences are lifted through the same positive witness. Paired target and
three direct module client builds pass with identical client objects; all 18 target
declaration reports, 55,241 simp entries and 23,370 instances match. Four
provider inputs lack current-source receipts and the wider closure includes an
older SignedPellResidue object. The directly importing umbrella was not rebuilt.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-carrier-set-iff-sharing-evidence/BUNDLE.json).

The object natural semiring witness sharing `483be9ee15` removes six net Lean
lines, bringing the reviewed series to 9993. Addition and multiplication share
the witness and induction argument, while their relation-specific steps are
selected with `first`. Paired target, ObjectResidualSquares and focused
ObjectOmegaSemiring check builds pass with identical client objects; all four
declaration reports, 32,692 simp entries and 14,590 instances match. The
directly importing umbrella was not rebuilt, and provider inputs remain cached
without current-source receipts. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-object-natural-semiring-evidence/BUNDLE.json).

The occupation selector sharing `f46e22674a` consolidates the repeated
selector-to-held-tile argument in a private helper. It adds one net Lean line,
bringing the reviewed series to 9992 net lines removed, but makes the two callers
shorter and names their common fact. Paired target and ArithmeticCellWindow
builds pass with identical client objects; all 70 existing declaration reports,
33,463 simp entries and 14,822 instances match. The transitive closure remains
cached; the evidence distinguishes historical provider objects from later
search-path samples. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-occupation-selector-sharing-evidence/BUNDLE.json).

The tiling band conditional simplification `e579fb28da` removes ten net Lean
lines, bringing the reviewed series to 10002. `split_ifs` and `simp_all`
follow the existing conditional priority and guards. The affected proof came
from Claude-coauthored commit `3cd04ac37f`. Paired target and
TilingWord client builds pass, and all 57 target and 18 client declaration
reports and sampled registrations match. The client object bytes differ for an
unknown reason; transitive dependencies remain cached. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261029-tiling-band-dispatch-evidence/BUNDLE.json).

The low-digit replacement sharing `3e1cc2606b` removes one net Lean line,
bringing the reviewed series to 10003. The affected proofs originated in
Claude-coauthored commit `5fcd5632b3`. A private lemma shares the bounded
replacement invariant across the subtraction and addition cases. Paired
WindowDigits and WindowBits builds pass with identical client objects; all 51
existing declaration reports, 28,973 simp entries and 13,172 instances match.
CyclicWord and MaskConstants were not rebuilt and the transitive closure remains
cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-window-digit-replacement-evidence/BUNDLE.json).

The cell-weight congruence simplification `68500896e1` removes five net Lean
lines, bringing the reviewed series to 10008. The affected proof originated in
Claude-coauthored commit `f79467f5448`. The modulo-16 fact follows from the
existing modulo-2048 fact. Paired CellLocal and CellLabels builds pass with
identical client objects; 232 common declaration reports and the sampled
registrations match. Two generated private names disappear and one is added;
the wider dependency closure remains cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-cell-weight-congruence-evidence/BUNDLE.json).

The run-trace head-step simplification `3735d55690` removes nine net Lean
lines, bringing the reviewed series to 10017. The affected proofs originated
in Claude-coauthored commit `5fcd5632b3`. The existing conditional cases use
the order simplifier and subtraction bound directly. Paired RunTrace and
TilingTable builds pass; 79 target and 73 client declaration reports and
sampled registrations match. Client object bytes differ for an unknown reason,
and the transitive closure remains cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-runtrace-step-bound-evidence/BUNDLE.json).

The rank order-lemma cleanup `062d55baa1` removes five net Lean lines, bringing
the reviewed series to 10022. The wrappers came from Claude-coauthored commit
`5fcd5632b3`; imported order facts now replace them at their call sites.
Paired RankForcing and RankForcing2011 builds
pass with identical client objects; nine retained declaration reports and the
sampled registrations match. The wrappers were unregistered, and transitive
dependencies remain cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-rank-order-cleanup-evidence/BUNDLE.json).

The rotation identity simplification `2fd68625e5` removes six net Lean lines,
bringing the reviewed series to 10028. It factors the quotient term before
using the existing exponent and quotient-remainder identities. Paired Packing
and both direct client builds pass; the checked declarations and registrations
match. ConstructionVariation objects match, while PackingCells objects differ
for an unknown reason; transitive dependencies remain cached. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261029-packing-rotation-evidence/BUNDLE.json).

The window prefix-tail simplification `6416d3a8d7` removes three net Lean
lines, bringing the reviewed series to 10031. The affected proof originated in
Claude-coauthored commit `5fcd5632b3`. A targeted left-side rewrite replaces
the intermediate congruence calculation. Paired WindowCarry and WindowInterface
builds pass with identical client objects; target and client declaration and
registration reports match. The transitive closure remains cached. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261029-window-carry-tail-evidence/BUNDLE.json).

The saturation order simplification `e9b2cb4040` removes four net Lean lines,
bringing the reviewed series to 10035. The affected proofs came from
Claude-coauthored commit `5fcd5632b3`. Additive cancellation and subtraction
positivity replace two contradiction arguments. Paired Saturation and
WindowInterface builds pass with identical client objects; declarations and
sampled registrations match. The transitive closure remains cached. See [the
evidence bundle](../../reviews/lean-proof-simplification-20261029-saturation-order-evidence/BUNDLE.json).

The binary half bound `55ddd54db0` removes three net Lean lines, bringing the
reviewed series to 10038. The proof applies the existing division inequality
directly. Paired target and all five tracked direct clients pass; the current
Saturation proof also passes against each phase's rebuilt Carry. Carry and
BinomLegendre object bytes differ for an unknown reason, while their checked
declarations and registrations match. The transitive closure remains cached.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-binary-half-direct-evidence/BUNDLE.json).

The Pell power recovery order cleanup `dab24627b9` removes six net Lean lines,
bringing the reviewed series to 10044. Two private wrappers are replaced by
imported order lemmas. Paired target and three direct clients pass with
identical client objects; retained declaration and registration reports match.
The separate combined FirstNorm-to-PowerRecovery replay also passes. Its
transitive closure contains an older PellResidueClasses object. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261029-pell-recovery-order-evidence/BUNDLE.json).

The first Pell norm bound simplification `541e94df32` removes two net Lean
lines, bringing the reviewed series to 10046. Positivity and the existing upper
bound imply the ordinate is one, eliminating an impossible zero branch. Paired
target and two direct clients pass with identical client objects. The combined
replay through the adopted PowerRecovery proof passes with identical objects;
the wider dependency closure remains cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-pell-first-positive-evidence/BUNDLE.json).

The cyclic rotation modulo simplification `5c94a5dd2d` removes three net Lean
lines, bringing the reviewed series to 10049. The affected proof originated in
Claude-coauthored commit `5fcd5632b3`. It uses the quotient-remainder identity
without an intermediate reordered decomposition. Paired target and three direct
clients pass; two client objects match, while WindowCarry objects differ for an
unknown reason despite matching checked interfaces. The transitive closure
remains cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-cyclic-rot-mod-evidence/BUNDLE.json).

The Pell square-order cleanup `c66364f0e2` removes twelve net Lean lines,
bringing the reviewed series to 10061. Three private duplicate proofs are
replaced with an imported nonnegative square-order lemma. Coherent paired
15-module replays cover all affected direct clients and both dependency paths;
all twelve unchanged downstream objects match. The 32 retained declaration
reports and sampled registrations match, and exactly three unregistered private
wrappers disappear. The wider closure remains cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-pell-square-direct-evidence/BUNDLE.json).

The Pell ordinate sum bound `20eb14ccb9` removes six net Lean lines, bringing
the reviewed series to 10067. Existing product lower bounds and `time_le_y`
give the sum comparison directly. Paired target and three direct clients pass
with identical client objects; target declaration and registration reports
match. The transitive closure remains cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-pell-y-add-evidence/BUNDLE.json).

The power perturbation identity simplification `a37047cc30` removes one net
Lean line, bringing the reviewed series to 10068. The affected proof came from
Claude-coauthored commit `90f67cbdd9`; a rewrite and cancellation replace its
three-step polynomial calculation. Paired target and four direct clients pass;
two client objects match and two differ for unknown reasons despite matching
checked interfaces. The transitive closure remains cached. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261029-pow-perturbation-evidence/BUNDLE.json).

The four-module positivity cleanup `75c50fe733` removes twelve net Lean lines,
bringing the reviewed series to 10080. Four private wrappers are removed and
their seven uses replaced with the imported positivity equivalence; two of the
wrappers came from Claude-coauthored commit `90f67cbdd9`. A coherent paired
replay covers the five direct clients and updated Pell, power and binomial
providers; unchanged client objects match. The 46 retained declaration reports
and sampled registrations match. A stale-provider lane was superseded and the
wider closure remains cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-four-positive-wrappers-evidence/BUNDLE.json).

The signed-pair unit-factor simplification `f37a2aad85` removes ten net Lean
lines, bringing the reviewed series to 10090. Positivity of the product and
divisibility of one replace two contradiction arguments and a multiplication
comparison. Paired target and three direct clients pass with identical client
objects; checked declaration and registration reports match. The wider closure
remains cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-signed-pairs-factors-evidence/BUNDLE.json).

The auxiliary-seed positivity simplification `0e833fe200` removes four net Lean
lines, bringing the reviewed series to 10094. Positivity of the existing products
replaces three zero-contradiction arguments. Paired target and three direct
clients pass with identical client objects; checked declarations and
registrations match. The transitive closure remains cached. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261029-auxiliary-seed-positive-evidence/BUNDLE.json).

The Pell positive-divisibility bound `1a0b5f209e` removes ten net Lean lines,
bringing the reviewed series to 10104. An imported lemma replaces a private
wrapper at its sole call site. Paired target and two direct clients pass with
identical client objects; five surviving declaration reports and sampled
registrations match. The private wrapper is removed; downstream construction
clients were not rebuilt and the wider closure remains cached. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261029-pell-integral-direct-evidence/BUNDLE.json).

The proof-word tail bound simplification `2cdde09b46` removes eight net Lean
lines, bringing the reviewed series to 10112. The affected proof came from
Claude-coauthored commit `d9775aa0f5b`. A direct nonnegative square comparison
replaces a contradiction chain. Paired target and ProofWordBound builds pass
with identical client objects; all 83 target declaration reports and sampled
registrations match. The transitive closure remains cached. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261029-level-square-direct-evidence/BUNDLE.json).

The residual-square symmetry simplification `227a58c783` removes three net
Lean lines, bringing the reviewed series to 10115. Commutativity directly
reuses the oriented square-gap identity. Paired target, three direct module
clients and the focused check pass; all three client objects and target reports
match. The umbrella importer was not rebuilt and some client inputs lack
source-matched receipts. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-residual-square-symmetry-evidence/BUNDLE.json).

The gcd-normalization positivity simplification `c0fb426562` removes sixteen
net Lean lines, bringing the reviewed series to 10131. Positivity of recorded
products replaces four repeated zero-contradiction arguments. Paired target and
three direct clients pass with identical client objects; all 29 target
declaration reports and sampled registrations match. The wider Pell and
construction closure was not rebuilt. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-gcd-product-positivity-evidence/BUNDLE.json).

The tiling colour numeral simplification `ab35b49240` removes six net Lean
lines, bringing the reviewed series to 10137. The affected proofs came from
Claude-coauthored commit `5fcd5632b3`. Direct conversion and numeral
normalization replace intermediate equalities in four existing bit branches.
Paired target and TilingRows builds pass; client objects differ for an unknown
reason, while the checked declaration and registration reports match. The
transitive closure remains cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-tiling-colours-direct-evidence/BUNDLE.json).

The fixed tiling-band edge simplification `85306187dc` removes four net Lean
lines, bringing the reviewed series to 10141. The affected proofs came from
Claude-coauthored commit `3cd04ac37f`. Existing reset cases simplify directly,
and the initial-column bound uses `lt_succ_iff_le`. Paired target and TilingWord
builds pass; client objects differ for an unknown reason, while the checked
declaration and registration reports match. The transitive closure remains
cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-tiling-band-fixed-evidence/BUNDLE.json).

The Pell coordinate-positivity simplification `477b3197a1` removes six net
Lean lines, bringing the reviewed series to 10147. Both norm proofs derive
positivity directly from their positive square. Coherent paired target and five
direct client builds pass with identical client objects; target declaration and
registration reports match. An older transitive Pell/GCD chain remains cached.
See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-pell-positive-reflect-evidence/BUNDLE.json).

The radix alignment positivity simplification `3f01d661e2` removes eight net
Lean lines, bringing the reviewed series to 10155. Exponential monotonicity and
product positivity replace two zero-contradiction arguments. Paired target and
both direct clients pass with identical client objects; eight target declaration
reports and sampled registrations match. An older transitive Pell chain remains
cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-radix-positivity-evidence/BUNDLE.json).

The squared-seed positivity simplification `11856f40e2` removes one net Lean
line, bringing the reviewed series to 10156. Product positivity replaces a zero
contradiction while retaining the coefficient witness and norm equation. Paired
target and both direct clients pass with identical client objects; target
declaration and registration reports match. Older objects appear in later
transitive path samples and the wider closure remains cached. See [the evidence
bundle](../../reviews/lean-proof-simplification-20261029-squared-seed-positive-evidence/BUNDLE.json).

The Wang bit-bound simplification `224acccf56` removes four net Lean lines,
bringing the reviewed series to 10160. The affected proofs came from
Claude-coauthored commit `64422b55f4`. Quotient, remainder and mod-two bounds
replace four bit case analyses. Paired target and five direct clients pass;
one client object matches and four differ for unknown reasons, while checked
interfaces match. The wider closure remains cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-wang-push-direct-evidence/BUNDLE.json).

The shared carry conversion `e8e12903c2` removes 28 net Lean lines, bringing
the reviewed series to 10188. One public `Facts.toMF` theorem replaces six
private wrappers and one inline conversion. Paired 18-module lanes pass,
including seven checks and four other clients. Two client objects differ for
unknown reasons while their checked interfaces match; the other checked client
objects match. The umbrella was not rebuilt and two external cached inputs lack
matched producer receipts. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-current-carry-to-mf-evidence/BUNDLE.json).

The carrier square-magnitude simplification `c110faf349` removes five net Lean
lines, bringing the reviewed series to 10193. Pair swapping reduces both order
cases to the same ring calculation. Paired target and three direct clients pass
with identical client objects; all 65 target declaration reports and sampled
registrations match. The historical transitive Pell chain and wider closure
remain cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-carrier-square-sharing-evidence/BUNDLE.json).

The high-digit lookup sharing `8e51af07d2` removes seven net Lean lines,
bringing the reviewed series to 10200. A focused facts module holds the block
decomposition and lookup proof previously repeated in three consumers, without
adding the lookup import to the common mask-data module. All thirteen tested
direct module clients pass with identical client objects; the umbrella was not
rebuilt. Named theorem reports and sampled registrations match, but 141 generated
public proof names disappear and 14 other generated reports change. A tracked
Lean/Python search found no references to the affected names. One cached provider
lacks a matched producer receipt; raw environment logs are omitted from the
compact archive. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-high-digits-module-sharing-evidence/BUNDLE.json).

The cell-label selector bound `a31bd9dc8c` removes five net Lean lines,
bringing the reviewed series to 10205. The affected proof came from
Claude-coauthored commit `f79467f5448`. A direct product bound replaces the
zero/one selector split. Paired target and CellTransfer builds pass with
identical client objects; non-generated declaration reports and sampled
registrations match. Two generated public proof names disappear and one changes
type; no tracked Lean/Python references were found. The wider closure remains
cached. See [the evidence bundle](../../reviews/lean-proof-simplification-20261029-cell-label-bound-evidence/BUNDLE.json).

The degree certificates of `ShortSystem`, `ShortFrontier` and `ShortReducedStrong` were replaced
independently of these packets, by the `total_degree_bound` tactic in `TotalDegreeBound`.
