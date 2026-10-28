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

The degree certificates of `ShortSystem`, `ShortFrontier` and `ShortReducedStrong` were replaced
independently of these packets, by the `total_degree_bound` tactic in `TotalDegreeBound`.
