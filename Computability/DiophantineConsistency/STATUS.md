# Research status

Updated 23 October 2026. This is a work log, not a completion certificate.

**Current direction:** Lean formalization is paused at the owner's request.
The active goal continues with equation-size and complexity reduction;
see [SIZE_REDUCTION.md](SIZE_REDUCTION.md). The Lean statuses below record
completed checkpoints, rather than instructions to continue formalization.

The first size-only result is a440-operation nine-positive circuit, down
from443, with the exact same polynomial and degree1,845,940; the natural
translation uses447 operations. Shared products and rank cancellation are
checked by exact local ring identities and a complete gate remap. See
[`gap2082-shared-products`](candidates/gap2082-shared-products/README.md).
The lower-degree package71 branch also saves three gates, reaching475
positive /482 natural operations at the unchanged degree1,379,730; see
[`order7-shared-products`](candidates/order7-shared-products/README.md).

Later saturation and an exact shared norm tail reach **433 operations at
degree1,628,768** with nine positive unknowns. The collected H1868 radical
form reaches **953 operations at degree999,518**. The original31 and
compact54 coefficient tuples remain separate storage tradeoffs. See
[`norm-tail-sharing`](candidates/norm-tail-sharing/README.md) and the
[latest review](PROPOSAL_REVIEW_LATEST.md). New complete positive-domain
points include ten variables/131 operations/degree1,152 and eleven/111/211.

The current [equation.pdf](equation.pdf), with standalone
[TeX](equation.tex), prints10 positive unknowns, exact degree368 and
101 operations, including all constants on one Letter page in9-point type.
It saves one operation and lowers degree by20 compared with the preserved
102/388 display. The entire closed fixed recipe is unchanged. Universal
formula binding, weighted-root/short-projector positive witness proofs,
complete native/controller transfer, independent coefficient regeneration,
both renderer modes and visual layout pass review; see the
[candidate](candidates/one-page-short10/README.md).
The [13-positive degree51 page](candidates/one-page-ordinary13/equation.pdf)
remains a different tradeoff.

The preserved fifteen-positive page prints a436-character base62 numeral
with its entire alphabet and positional sum. Its complete coefficient
recipe has2297 nonwhite characters, down from2518 on the preserved771-digit
page and2861 on the original page. A decimal-only merged-mask recipe has
2482 characters; an original-tuple base62 variant has2424. All pages include
standalone TeX/PDF; every decoded action, coefficient byte and printed
payload character passes normal/optimized checks. Numeral notation and
information compression are distinguished in
[SEED_PREDICTORS54.md](SEED_PREDICTORS54.md). The renamed tuple changes K;
[SEED_COMPRESSION54.md](SEED_COMPRESSION54.md) supplies its ordinary conjugacy proof.

The [ordinary-norm twelve-positive equation](research/ordinary-unit-products/README.md)
has a literal100-operation circuit of exact degree70. Its
[free-J polarized successor](candidates/free-j-polarized-positive/README.md)
now uses96 operations at the same degree. The congruence proof carries the
possible factor three until power recovery, and the tail rewrite is an
exact polynomial identity. Its ordinary
proof establishes the strong-rank bound before using the norm merger;
normal/optimized independent circuit, identity and degree checks pass.
The101/78 and thirteen-positive90/55 checkpoints are retained in
[`short-unit-products`](research/short-unit-products/README.md).
The ordinary strong-norm variant improves the thirteen-positive form to
90 operations and exact degree51; see
[ORDINARY13.md](research/ordinary-unit-products/ORDINARY13.md).

The combined [centered joint22](candidates/joint22-centered/README.md)
equation has22 unrestricted integer unknowns, exact degree14 and119 live
gates. Complete inverse row transformations, the whole six-port binding,
literal DAG and coefficient-independent leading form pass exact checks.

The [wave11 review](PROPOSAL_REVIEW_WAVE11.md) is complete for its stated
release/component scopes: accepted new points include eleven-positive
111/277 and114/257, ten-integer480/1,245,324 and37-integer quartics.
The separate report-only811-operation nine-variable claim lacks its
referenced section/artifacts and is not counted as a checked endpoint.
The [Hilbert Tenth transfer](candidates/fixed-root-elimination/README.md)
now gives14-positive73/342 and75/293 equations. Their signed-root
specialization, full literal circuits and coefficient-independent degree
witnesses pass separate ordinary review and normal/optimized checks.
All Lean work remains paused.

The [centered Hilbert Tenth transfer](candidates/fixed-root-centers/README.md)
adds fourteen-positive74/312 and76/191. Its ordinary version proves deleted
rational-root integrality after exposing the early main Pell bound, then
restores the signed source and positive inverse. Separate ordinary review
and exact normal/optimized algebra checks pass.

The [synchronized direct review](PROPOSAL_REVIEW_SYNCHRONIZED_CERTIFICATES.md)
accepts522/529/596/895-natural-variable quartics with a common Pell frame
and radix, after full ordinary review and normal/optimized rebuilding.
Our [actual-row guard family](candidates/synchronized-row-guards/README.md)
gives1,224/1,231/1,298/1,597 unrestricted integer variables. Every omitted
guard is justified by its exact integer row certificate before arithmetic
interpretation. [Signed projection](candidates/synchronized-signed-projections/README.md)
then reaches1,190 integers,26,411 terms and height83,900,628. Complete
reverse restoration recovers every original guard and sign condition.
The separate [batched direct review](reviews/batched-direct-peer.md)
also accepts its1,690-integer companion; signed projection produced
seven complete synchronized tradeoff points, now retained as checkpoints.
All are degree4. Lean remains paused.

The historical [direct C222 quartic](PROPOSAL_REVIEW_DIRECT_C222_ROUND12.md) is a
complete ordinary alternative independent of K215, native coefficients
and Jones. Its52-stage incoming replay and ordinary proof passed separate
reviews. The newer [shared-direct construction](PROPOSAL_REVIEW_SHARED_CERTIFICATES_DIRECT.md)
and [prime-power CRT lift](candidates/shared-crt-prime-lift/README.md)
reduce the natural-variable count from16,036 to3,609. Reusing the actual
[beta majorant](candidates/shared-crt-beta-majorant/README.md) reduces it
further to3,603; the endpoint supplies the needed index bound before CRT.
The complete
[integer companion](candidates/shared-crt-prime-lift/integer/README.md)
has8,619 variables,39,811 monomials and coefficient height127,285,349,
compared with27,916 variables in the original. Full coefficient files,
ordinary correctness arguments and independent normal/optimized checks
are committed. The new Lean/internal-ZFC compilation theorem remains open.

[Thirteen-integer root fusion](PROPOSAL_REVIEW_ROOT_FUSION13.md) and
[fixed-prime radicals](PROPOSAL_REVIEW_FIXED_PRIME_RADICALS.md) now pass
ordinary reviews and normal/optimized release replays. Exact
[compact norm evaluators](candidates/fixed-prime-compact-norms/README.md)
save277 operations for five roots and67 for four without changing any
polynomial. Useful fourteen-integer points include148/748,156/664 and
163/652; the root-fusion thirteen-integer points remain cheaper than the
fixed-prime counterparts. Both newer [parity families](PROPOSAL_REVIEW_PARITY_FAMILIES.md)
now pass small-integer ordinary reviews and scoped normal/optimized
replays, adding fifteen-integer128/204 and124/352, and sixteen-integer
119/112 and115/160. The [prime-separation review](PROPOSAL_REVIEW_PRIME_SEPARATION.md)
adds16/108/132 as a lower-degree, greater-cost choice. Fixing the positive
power bound to`W=n+k` gives direct quartics with3,443 or5,960 natural
variables; its [ordinary proof](candidates/shared-crt-fixed-power-bound/PROOF.md)
constructs fresh Pell witnesses at every common bound. Full literal and
normal/optimized checks pass. These do not yet replace the frozen integer
companion. No global optimality claim is made.

The historical manuscript collection has moved from the Cardinals reports
tree to [con-zfc-diophantine-forms](con-zfc-diophantine-forms/README.md),
at the repository owner's request. Live catalogue/intake/research links
were updated. Pinned historical source paths remain valid for their named
commits and are deliberately retained in the delivered provenance records.

| Component | Status | Evidence / next task |
|---|---|---|
| Reports and historical comparison | Initial audit complete | Wave-5 collection README; P67 circuit in package 36 |
| Wave-6 reports | Merged; comparison started | Packages 38–45 placed by `124c07c0b7`, merged at `2d7766807b`; direct quadratic coding is a further size-reduction route |
| Wave-7 proposals and target review | Historical target retained as checkpoint | Packages 46–53 at `6d375f2d2d`, merged at `d869b0ddbf`; selected package 52's nine-positive 548-operation form at that stage; see `PROPOSAL_REVIEW.md` |
| Wave-8 proposals and proof checkpoint | Reviewed; checkpoint preserved | Packages 54–59 at `beb0192cb8`; all six full finite replays PASS; package 59 adjunct has nine positive variables, 473 operations, degree 1,910,404; see `PROPOSAL_REVIEW_WAVE8.md` |
| Wave-9 proposals and next numerical targets | Reviewed | Packages 60–67 at `a2cd79b912`; all eight full normal release replays PASS; delivered nine-positive cost target 66:444/1,845,940; separate compact54-sharp instance passes sealed replays at 443 positive / 450 natural operations, same degree; see `PROPOSAL_REVIEW_WAVE9.md` |
| Wave-10 proposals | Reviewed | Packages68–75 at `d79b41884d`; all8 full normal releases PASS; new38-integer quartics,11-positive325/113 and nine-positive1,379,730/478 alternatives; current443-operation target retained; see `PROPOSAL_REVIEW_WAVE10.md` and both detailed replay receipts |
| Compact split-form coefficient instances | Generated and independently replayed | Whole package-54 / package-57 tuples, same 473 operations and degree 1,910,404; preferred sharp native payload 215,492 raw bytes and live derived constants 1,672,725 bytes; see `candidates/split116-compact/README.md` |
| Split-form generic source contract | Lean checked | Full binomial-to-bounded-source-coefficients equivalence, derived degree/quarter bounds, unconditional word positivity and exact outer ratio; native calibration remains separate; see `SPLIT116_FORMALIZATION.md` |
| Literal split116 source and unbounded nine-coordinate equivalence | Lean checked | `SplitNineSource59.exists_natural_zero_iff_source_compact54`: exact authoritative old-z source, all 89 kernel records, four explicit port boxes; no supplied height, degree, packing or population premise; see `SPLIT_SOURCE59.md` |
| Literal split116 nine-variable polynomial | Lean checked | `SplitNinePolynomial59`: actual `MvPolynomial (Fin 9) Int`, ring-map and natural evaluation identities, source-zero iff; literal480 natural DAG identified with recipe in `SplitCircuitRecipe59` |
| Shared split116 base powers | Lean checked | Exact generic-ring and MvPolynomial rewrite at456/463 positive/natural operations, full liveness/counts; both polynomials identified with source recipe including all12 fixed-leaf expressions; positive/natural root equivalence checked; see `SPLIT_POSITIVE_RECIPE59.md` |
| H2082 affine positive source change | Lean checked | `GapSource66.positiveZeroEquiv` and `exists_positive_nat_zero_iff` preserve the full positive zero set by explicit inverse maps, using only literal source rows and beta positivity; no Pell or native calibration premise; see `GAP_SOURCE66.md` |
| H2082 literal extraction and kernels | Lean checked | `GapGeometry66`, `GapCertificate66`, `GapKernelData66`, `GapKernels66`: all85 records and22450 degree-matched interactions, exact source-zero extraction, sharp four-port height and degree≤2082; see `GAP_KERNELS66.md` |
| Compact H2082 ratio calibration | Lean checked | `GapNineRatio66`: block exponent2200, threshold `2^(15*a+79)*B^1162`, half-height a; exact population calibration including b=1, derived finalizer bounds and sound/complete ratio; see `GAP_NINE_RATIO66.md` |
| H2082 unbounded nine-coordinate source equation | Lean checked arithmetic endpoint | `GapNineSource66.exists_natural_zero_iff_source_compact54`: all source bounds/carry/ranges derived, explicit cofinal witnesses, half-height432007 and four port boxes; `compact54_zero_iff_split59` compares old/new unbounded zero existence under beta positivity; native calibration remains separate; see `GAP_SOURCE_NINE66.md` |
| H2082 actual nine-variable polynomial | Lean checked | `GapNinePolynomial66`: actual `MvPolynomial (Fin 9) Int`, every85 coefficient record, generic scalar/map identities, natural evaluation/source equivalence and old-polynomial zero equivalence; native calibration remains separate; see `GAP_NINE_POLYNOMIAL66.md` |
| H2082 counted positive/natural circuits | Lean checked | `GapCircuitRecipe66`, `GapCircuitTranslation66`, `GapPositiveRecipe66`: actual443/450 DAGs identified with scalar and MVP source recipes, all11 fixed leaves bound coherently, complete positive/natural root correspondence; see `GAP_CIRCUIT_RECIPE66.md` |
| H2082 cancellation-aware degree | Lean checked upper bound | `GapPolynomialDegree66`: actual443/450 polynomials and source recipes have degree≤1,845,940; checked484 local labels plus Pell-defect and recentering cancellations; exact-degree lower bound remains a finite-audit result; see `GAP_DEGREE66.md` |
| Signed native Pell step-down | Lean checked | `NativePellStepDown`: signed minus-form index recovery and safe strong-quotient restoration; recovered main sequence and bootstrap hypotheses remain explicit; see `NATIVE_PELL_STEP_DOWN.md` |
| Literal native Pell bootstrap and index | Lean checked | `NativePellBootstrap.source_main_index_exact`: main classification, native window bounds, strong bootstrap and exact native index from literal old-z source and native port relations; payload/compiler calibration remains separate |
| Native first index and binary scale | Lean checked arithmetic prerequisites | `NativePellFirstIndex`, `NativePellPower`, `NativeBinaryScale`, `NativePellScaleBounds`: exact odd first index, actual source `X=2^R`, `q=(2^d)^N` and cubic common scale; subsequent half-binomial and arithmetic-window extraction checked; whole fixed-payload/compiler calibration remains open; see `NATIVE_PELL_POWER.md` |
| Literal source to native arithmetic window | Lean checked forward bridge | `NativeHalfBinomial`, `NativePopulationLower`, `NativeMaskPopulation`, `NativeSourceMask`, `NativeSourceWindow`: doubled ratio, exact saturation/mask tests, radix/repunit, spatial power and old-z transport derived from actual source under explicit coefficient interface; whole-tuple Wang/K215 binding and converse completeness remain open; see `NATIVE_SOURCE_WINDOW.md` |
| Compact54 native local clause decoder | Lean checked | `NativeSelectorClause54.native_clause_iff`: arbitrary Boolean457-selector assignments force exactly empty or one allowed tile, complemented copied labels and synchronized anchors; actual coefficient recipes and pinned literal modes checked; global convolution/phase/compiler bridge remains open; see [NATIVE_CLAUSE54.md](NATIVE_CLAUSE54.md) |
| Compact54 whole-stencil convolution carry step | Lean checked forward bridge | `NativeWindowConvolution54.source_convolution_mask_digits`: exact1045-term stencil/mass, every binary rotation phase, derived no-carry and source transport produce pointwise mask tests under explicit word/port bindings; assignment-support, phase/basis synchronization and machine calibration remain open; see [NATIVE_CONVOLUTION54.md](NATIVE_CONVOLUTION54.md) |
| Native low mask and Start origin | Lean checked forward bridge | `NativeLowPort54` proves the symbolic exactMC recipe and low digitρ−2; `NativeSourceOrigin54` derives C modρ=1 from actual source masks and c0=1 for a supplied digit word; full support extraction/basis/phase remains open; see [NATIVE_ORIGIN54.md](NATIVE_ORIGIN54.md) |
| Native source to sparse assignment | Lean checked forward bridge | `NativeSparseDigits54.source_assignment_exists` extracts positive cell count, wordC, origin1 and exact periodic capacities; off-support0, all except dummy507 Boolean; `source_sparse_convolution` discharges assignment hypotheses of the convolution bridge; exact coefficient interface/K/high-mask bindings and phase/global calibration remain explicit; see [NATIVE_SPARSE_DIGITS54.md](NATIVE_SPARSE_DIGITS54.md) |
| Literal native clause bands | Lean checked forward bridge | `NativeCleanBands54` identifies whole1045-term cyclic convolution at2409/3015 with its literal local coefficient sum plus explicit temporal contribution; all opposite/copy/spatial contributions excluded by derived sparsity, including one-cell collisions; MF binding/phase/global tableau interpretation remain open; see [NATIVE_CLEAN_BANDS54.md](NATIVE_CLEAN_BANDS54.md) |
| Actual native local mask before alignment | Lean checked forward bridge | `NativeHighPort54` binds all31 MF digits, bounds/residues/population520 and repeated high-mask word; `NativeTemporalSupport54` proves one clause band is uncontaminated at every cell for every bit phase; `NativeLocalMask54.source_local_masks` gives the actual localCell mask zero with no alignment/accepted-clause premise; coefficient Interface/K binding and global calibration remain explicit; see [NATIVE_HIGH_PORT54.md](NATIVE_HIGH_PORT54.md) and [NATIVE_TEMPORAL_SUPPORT54.md](NATIVE_TEMPORAL_SUPPORT54.md) |
| Exact meaning of consistency | Identified | `¬ BProv ZFCax_s [] Form.fBot`; existing unconditional K215 endpoint |
| Concrete recursively enumerable refutation predicate | Lean checked | `Computability.refutationInputs_re` and `Bridge.zfcRefutationInputs_re`; actual six-register enumerator |
| Direct sealed-ZFC proof checker | Lean checked | `AnnotatedProofChecker.exists_refutation_iff`: executable parent-index certificates with explicit axiom/schema tags, exactly the original17 rules; no K215/Jones dependency, no choice in data or audited proof |
| Direct checker numeric encoding | Lean checked | `AnnotatedProofCode.exists_checked_code_iff`: total fuel parser, typed roundtrips, unique decoded quote, truncation rejection, and exact numeric refutation existence; complete PR/graph compilation and internal-code transport remain open |
| Direct checker local PR arithmetic | Lean checked | `AnnotatedCodeArithmetic`: literal ScalarPRCode data for tree constructors/projections, guarded list lookup and exact context+formula reference checking; full checker compilation remains open |
| Direct checker renaming certificates | Lean checked | `AnnotatedRename` and `AnnotatedRenameCode`: finite numeric tables for actual shift/instantiation under arbitrary binder depth, exact soundness/completeness, guarded references; whole-table PR program now checked in `AnnotatedRenameScanPR`, 3605 nodes / 3329 after certified optimization; internal model-omega interpretation remains open; see `ANNOTATED_RENAME_VALIDATOR.md` |
| Direct checker additive bound and sealing certificates | Lean checked external arithmetic | `AnnotatedBoundScan.exists_seal_program_iff`: exact numeric certificates for actual `bound` and `sealF`; whole sealing PR program2279 nodes /1983 optimized; axiom dispatch, proof-line validation and internal coding remain open; see [ANNOTATED_BOUND_SEAL.md](ANNOTATED_BOUND_SEAL.md) |
| Direct checker actual schema programs | Lean checked external arithmetic | `AnnotatedSchemaMaps`, `AnnotatedSchema`, `AnnotatedReplacement`: all four actual variable maps, literal body assembly, raw-input schema validation and sealing; exact existential languages for actual sealed Separation/Replacement axioms,10241/25535 program nodes; axiom dispatcher, full proof-line validator and internal code transport remain open; see [ANNOTATED_SCHEMAS.md](ANNOTATED_SCHEMAS.md) |
| Direct checker context arithmetic and assumption rule | Lean checked external arithmetic | `AnnotatedContextPR` recovers actual contexts and exact shifts from raw inputs, `AnnotatedContextLookup` checks actual quoted-context members, and `AnnotatedAssumption` agrees with the original rule and yields actual `Prov`; full context4177/3855 and assumption4753/4391 raw/optimized program nodes; remaining rules, loop, axiom dispatch and internal transport stay open; see [ANNOTATED_CONTEXT_RULE.md](ANNOTATED_CONTEXT_RULE.md) |
| Shared actual-rule coordinates and output/premise programs | Lean checked external arithmetic | `AnnotatedRuleCoordinates`/`AnnotatedRuleSchedules`: raw validation, exact output and ordered premises for all17 original rules, literal inverse embedding, supplied PR selectors; side/parent/loop now composed in the scanner checkpoint below; axiom dispatch/internal transport remain open; see [ANNOTATED_RULE_COORDINATES.md](ANNOTATED_RULE_COORDINATES.md) |
| Full numeric logical proof scanner | Lean checked external arithmetic | `AnnotatedParents`/`AnnotatedRuleSide`/`AnnotatedLine`/`AnnotatedLineScan`: raw acceptance recovers actual provable judgment; existential acceptance iff original `Prov G a` for all17 rules, supplied24891-node/23017-optimized program; sealed axiom context and internal transport remain open; see [ANNOTATED_LINE_SCANNER.md](ANNOTATED_LINE_SCANNER.md) |
| Complete numeric sealed-ZFC refutation checker | Lean checked external arithmetic | `AnnotatedRefutationPR.exists_refutation_iff`: closed supplied unary program accepts some raw certificate iff `BProv ZFCax_s [] fBot`; exact9-case axiom/schema dispatcher and full context scan,83281/76313 raw/optimized nodes; smaller shared graph and internal nonstandard-code interpretation remain open; see [ANNOTATED_REFUTATION_PR.md](ANNOTATED_REFUTATION_PR.md) |
| Sharp pairing quartic on internal omega | Lean checked internal semantics and ZFC derivations | `ObjectPairingSyntax` binds the actual4 residuals to the exact graph; `ObjectPairingGraph` proves totality/functionality, `ObjectPairingSurjective` proves every internal code has a pair decomposition by definable induction; corresponding sealed sentences have unconditional ZFC proofs; full checker code transport remains open; see [OBJECT_SHARP_PAIRING.md](OBJECT_SHARP_PAIRING.md) |
| Literal numeric wire quartics on internal omega | Lean checked internal semantics | `ObjectPredecessorSyntax` proves the actual predecessor quartic graph and ZFC totality; `ObjectTreeCodeSyntax` binds both actual5-auxiliary projection quartics on all internal inputs; `ObjectZeroTest` binds the actual1-auxiliary zero-test quartic; full internal checker transport remains open; see [OBJECT_NUMERIC_WIRE.md](OBJECT_NUMERIC_WIRE.md) |
| Guarded numeric wire quartics on internal omega | Lean checked internal semantics | `ObjectConditional` binds the actual2-auxiliary conditional; `ObjectListHead` binds the actual7-auxiliary guarded head with derived internal bound/completeness; degree≤4, nil/found-zero semantics retained; see [OBJECT_NUMERIC_WIRE.md](OBJECT_NUMERIC_WIRE.md) |
| Smaller syntax-constructor graphs | Lean checked local graphs and metadata | `AnnotatedSyntaxGraphs.forkGraph` uses3auxiliaries/54ops/degree≤4 vs old8auxiliaries; syntax-directed composed formula graphs have exact5*forkCount witnesses without huge numeral coefficients; full composed degree/shared-context compiler remains separate; see [ANNOTATED_SYNTAX_GRAPHS.md](ANNOTATED_SYNTAX_GRAPHS.md) |
| Shared-row syntax constructors | Lean checked quartic compiler and counts | `AnnotatedSharedSyntax` supplies actual Tree/Form quartics,4*forkCount witnesses and4*forkCount+1quadraticrows; exact7fixed-body counts84/84/108/104/108/188/264 via syntax metadata, no huge quoted coefficients; full checker composition remains open; see [ANNOTATED_SHARED_SYNTAX.md](ANNOTATED_SHARED_SYNTAX.md) |
| Euclidean division in internal omega | Lean checked semantics and ZFC totality | `ObjectDivision` proves existence/uniqueness by displayed-formula induction and numeral division/modulo compatibility; `ObjectDivModSyntax` binds actual1-slack guarded quartic on all internal naturals,degree≤4; internal trace/compiler calibration remains open; see [OBJECT_DIVISION.md](OBJECT_DIVISION.md) |
| Nine-variable specialization | Lean checked | `zfcNinePolynomial_noZero_iff_conZFC`, no premises; existence-based coefficients |
| Quartic alternative | Lean checked | `zfcQuarticPolynomial_noZero_iff_conZFC` and total degree at most four |
| Direct executable quartic without Jones compression | Lean checked external endpoint | `DirectQuarticZFC.noNaturalZero_iff_conZFC`, actual syntax/polynomial evaluation identity and degree at most four; `QuarticCost` proves at most `6*(nu+1)` tree operations; numerical `nu` remains unmeasured; see `ALTERNATIVE_ENCODINGS.md` |
| Closed direct-quartic size bound | Lean checked conservative bound | `DirectQuarticSize.variableCount_lt`: actual compacted natural-variable count `<2^300000`, from source witness count plus one≤`2^22426`, depth≤140000 and exact bounded-iteration metadata; exact count remains unmeasured; see `NATIVE_QUARTIC_SIZE.md` |
| Shared arithmetic DAG to quartic | Lean checked compiler | `DAGQuartic.exists_polynomial_zero_iff`: arbitrary signed intermediates, `n+2*m` natural slots, degree≤4, at most `12*m+4` tree operations; complete proof checker compilation remains open; see `DAG_QUARTIC.md` |
| Nonnegative arithmetic DAG to quartic | Lean checked compiler | `NaturalDAGQuartic.exists_polynomial_zero_iff`: two-output equality, nonnegative constants and addition/multiplication, `n+m` natural slots, degree≤4 and at most `6*m+4` tree operations; whole-checker compilation remains open |
| Supplied shared natural-register builder | Lean checked | `NaturalRegisterProgram`: literal/input/add/mul constructors append one register, old values and sharing preserved; output equality gives actual `Rep` with exactly m gate witnesses, degree≤4, operations≤6m+4; concrete shared-square regression checked; whole checker compilation remains open; see `NATURAL_REGISTER_PROGRAM.md` |
| Shared-register existential scopes and pairing graphs | Lean checked | `NaturalRegisterRelation` compiles explicit auxiliary inputs with exactly k+m witnesses; `RegisterNatPairing` covers the direct checker's actual max-square `Nat.pair/unpair` (41 witnesses, degree≤4, ≤238 operations per projection), `RegisterCantorPairing` separately covers the older enumerator (11 witnesses, ≤64 operations); whole checker compilation remains open; see [SHARED_REGISTER_RELATIONS.md](SHARED_REGISTER_RELATIONS.md) |
| Quadratic constraints on shared registers | Lean checked compiler and local reductions | `QuadraticRegisterSystem` adds no gate witnesses for supplied quadratic rows; exact max-square pairing3 witnesses, each unpair projection4/46 operations, guarded joint div/mod1/16, all degree≤4; complete checker composition and internal interpretation remain open; see [QUADRATIC_REGISTER_SYSTEM.md](QUADRATIC_REGISTER_SYSTEM.md) |
| Composable sharp checker tree/list graphs | Lean checked | `QuadraticRegisterComposition` retains shared registers and auxiliary context; actual `treeLeft`, `treeRight` and guarded `listTail` each5 witnesses,62 operations,degree≤4, including nil0; prior witnesses/operation/syntax-degree tradeoffs kernel checked; whole checker composition remains open; see [QUADRATIC_TREE_CODE_GRAPHS.md](QUADRATIC_TREE_CODE_GRAPHS.md) |
| Guarded checker arithmetic | Lean checked local quartics | `QuadraticBoolean` supplies zero-test1w/20ops and conditional2w/32ops; actual `QuadraticListHead`7w/76ops, all degree≤4, including nil0 and found-zero1; earlier11w/8231ops/syntaxdegree≤1024 baseline checked; complete checker compilation remains open; see [QUADRATIC_GUARDED_GRAPHS.md](QUADRATIC_GUARDED_GRAPHS.md) |
| Explicit, computable coefficient recipe for ZFC | Lean checked | `ExplicitZFC.expression` is a closed executable definition; numerical payload not materialized |
| P67 compiler correctness in Lean | Open | The report's ordinary proof is not yet a Lean proof |
| Object-level ZFC derivation | Open | External equivalence and internal provability are separate claims |
| Completely specified one-page equation | Checked presentation and coefficient identities | `candidates/one-page/equation.pdf`: one Letter page, exactly15 positive unknowns, no external coefficient data,1294-digit action seed plus fixed sums/powers/integer division; all4whole compact54 ports byte-identical, packed seed bound to actual Lean dense215; ordinary P69 calibration documented, end-to-end Lean/internal-ZFC theorem remains open |
| One-page arithmetic mode rank | Lean checked finite binding | `OnePageModesData54`/`OnePageModes54`: literal seed/templates form457modes; printed fixed sum of integer quotients computes each exact sorted native index and preserves the whole label/kind; MC support/subtraction bound separately; see [ONE_PAGE_TUPLE54.md](ONE_PAGE_TUPLE54.md) |
| Global simplicity minimum | Not claimed | No common ordering of all size measures; no optimality theorem |
| Short-equation local simplification | Lean checked | `ShortEquation.scaled_zero_iff_reduced`, no compiler hypothesis |
| Literal 69-operation polynomial | Lean checked | `ShortCircuit.eval_polynomial_zero_iff_baselineValue_zero`; scalar and MvPolynomial evaluation both included |
| Literal 75-operation polynomial, degree 68 | Lean checked | `ShortSystem.eval_compactPolynomial_zero_iff_baselineValue_zero` and `compactPolynomial_totalDegree_le` |
| Literal 73-operation polynomial, degree 80 | Lean checked | `ShortFrontier.eval_polynomial_zero_iff_baselineValue_zero` and `polynomial_totalDegree_le` |
| Literal 76-operation polynomial, degree 64 | Lean checked | `ShortReducedStrong.value_zero_iff_compactValue_zero` for all integer assignments; actual polynomial and degree bound checked |
| Consecutive-product negative Pell obstruction | Lean checked | `ConsecutivePell.norm_ne_neg_one` for every integer `n ≥ 2` |
| Executable representation data | Lean checked primitives; integration open | `Representation`, `ArithmeticRepresentation`, `NaturalExpression`; see `COMPILER.md` |
| Explicit arithmetic and bounded quantification | Lean checked | Supplied Pell, power, binomial, factorial and bounded-forall representations; no representation selected from existence proofs |
| Supplied representation to nine-variable equation | Lean checked | `EquationFromRep.construct`: explicit normalized quartic, literal index, expression and polynomial, natural solvability/unsolvability equivalences |
| Executable supplied-data Jones compiler | Lean checked | `ExecutableJones.fromRep`, sparse coefficient reader, explicit coding sums/index; exact evaluation agreement with the mathematical polynomial |
| Primitive-recursive graph compiler | Lean checked | `ScalarPRCode.graphRep`, structural on all seven program constructors, including the full bounded transition trace |
| Concrete refutation-program data | Lean checked | `DirectEnumerator.program : ScalarPRCode.Realizes haltingTest`, constructed directly from arithmetic source semantics |
| Closed executable consistency equation | Lean checked | `ExplicitZFC.noSyntaxZero_iff_conZFC` and `noNaturalZero_iff_conZFC`, with no supplied-data hypothesis |
| Closed equation from direct arithmetic graphs | Lean checked | `NativeZFC.noNaturalZero_iff_conZFC`; native Cantor/branch graphs and one outer iteration trace |
| Native formula blocks and direct composition | Lean checked | One-step source graph reduced from 6,924 through 1,811 to 1,742 witnesses; complete quartic/Jones counts remain unmeasured |
| Nine strictly positive integer unknowns | Lean checked | `PositiveZFC.noPolynomialZero_iff_conZFC` and the exact natural-to-positive shift |
| Polynomial-size quadratic positions | Lean checked foundation | `SidonPositions`: explicit cubic-size weights, exact unordered-pair uniqueness; full quadratic/Jones adaptation remains open |
| Quadratic coefficient extraction | Lean checked foundation | `QuadraticCoding`: the complementary encoding extracts twice each supplied quadratic value at a cubic-size position |
| Simultaneous quadratic extraction | Lean checked foundation | `MultiQuadraticCoding`: one combined polynomial recovers every supplied quadratic row, with a bound linear in rows and cubic in source dimension |
| Simultaneous quadratic carry test | Lean checked foundation | `MultiTargetCarry`: exact rowwise zero test by one central-binomial divisibility condition, under explicit coefficient and packing bounds; see `QUADRATIC_CODING.md` |
| Support-sensitive quadratic extraction | Lean checked | `SelectiveQuadraticCoding`: arbitrary weights and row targets; unused pairs may collide and row intervals may overlap |
| Literal selective position certificates | Lean checked | `SelectiveCertificate46` protects 62 pairs; `SelectiveCertificate52` protects 71 and supplies regular-target extraction on that support |
| Literal package-52 quadratic source | Lean checked | `NativeQuadraticParent`: exact 60 gates, 22 rows, 136 coefficient records and equality with the actual positive source; see `SELECTIVE_SOURCE52.md` |
| Package-52 positions and coefficient height | Lean checked | `NativeQuadraticPositions`: exact kernel degree 7,516 and product degree below 7,865; `NativeCoefficientBounds`: corrected coefficients below `2^1182955` under explicit port bounds |
| Sparse low-mask decoding | Lean checked | `LowMaskCoding`: exact arbitrary-position encoding, unused digits zero, actual input weight zero and dummy position 81 covered |
| Selective coefficient and packing bounds | Lean checked | `SelectiveCarry`, `SelectiveCoefficientBounds`, `PolynomialRangeBounds`: full polynomial, half-base, pre-decoding range and two-block central-binomial contracts |
| Package-52 ratio substitution and finalizer | Lean checked | `NativeNineRatio52` and `NativeNineFinalizer52` close the exact arithmetic tail against the existing Jones theorem |
| Assembled package-52 arithmetic source contract | Lean checked | `NativeQuadraticSource52.source_contract` and `NativeNineSource52.natural_zero_iff_source_published`; nine natural coordinates, explicit four-port size bounds |
| Literal package-52 source-equivalent polynomial | Lean checked | `NativeNinePolynomial52`, `NativeNineEquation52.exists_zero_iff_source_published`; actual `MvPolynomial (Fin 9) ℤ`, no truncated arithmetic; native calibration and shared-evaluator count remain separate |
| Native arithmetic source elimination | Lean checked | `NativeArithmetic52`: explicit 31-to-16 coordinate lift and seven residuals, preserving positivity conditions; old transport conventions require their own domain translation |
| Sharp majorant and two-root finalizer | Lean checked | `NearSquareFinalizer.exists_value_zero_iff` gives two square tests, divisibility and positive margin; source packing and native calibration remain separate |
| Ordinary-strong minimum-norm finalizers | Lean checked local theorem | `MinimumNorm.gap_minima75_zero_iff` / `gap_minima76_zero_iff` formalize package 47's local minimum arguments; literal circuit and native rank/calibration bridges remain separate |
| Internal ZFC addition | Lean checked | `ObjectArithmetic.zfc_proves_addition_total` and `zfc_proves_addition_unique` are actual `BProv` derivations; see `OBJECT_ZFC.md` |
| Internal addition laws | Lean checked | `ObjectAdditionLaws` and `ObjectAdditionCancellation`: definable-induction proofs of zero/successor, commutativity, associativity, cancellation and zero-sum criterion on every internal natural; actual closed ZFC derivations of commutativity/associativity/cancellation; see `OBJECT_ADDITION_LAWS.md` |
| Internal multiplication and natural expressions | Lean checked | Actual ZFC totality/functionality proofs in `ObjectMultiplication` and `ObjectNaturalExpression`; `ObjectMultiplicationLaws` and `ObjectDistributivity` prove all-internal-omega zero/successor/commutativity/associativity/distributivity with actual closed ZFC derivations |
| Actual polynomial-side object sentence | Lean checked | `ObjectEquation.unsolvabilitySentence`, exact semantics over all internal natural tuples; the internal consistency iff is still open |
| All-model semiring interpretation | Lean checked | `ObjectOmegaSemiring` packages the entire internal omega as a nontrivial commutative semiring; `ObjectNaturalSemiring` identifies actual expression/equation/no-zero formula semantics with semiring evaluation, including nonstandard tuples; arbitrary external arithmetic transfer is not supplied; see `OBJECT_OMEGA_SEMIRING.md` |
| Internal sum-of-squares compiler step | Lean checked actual ZFC derivation | `ObjectNaturalOrder`, `ObjectNaturalZero`, `ObjectResidualSquares`: internal differences, canonical ordered cancellation, no zero divisors and exact finite residual conjunction; `zfc_proves_residual_conjunction` covers every internal natural tuple; complete representation/consistency equivalence remains open; see `OBJECT_RESIDUAL_SQUARES.md` |
| Internal literal tree-to-quartic compiler | Lean checked actual ZFC derivation | `GatesSemiring`/`QuarticSemiring` identify the actual stored residuals over arbitrary semirings; `ObjectQuarticCompiler.zfc_proves_compiler` proves equivalence of actual source/compiled no-zero sentences over entire internal omega, with actual target degree≤4; full proof-checker representation/internal consistency calibration remains open; see [OBJECT_QUARTIC_COMPILER.md](OBJECT_QUARTIC_COMPILER.md) |
| Unbounded internal consistency sentence | Lean checked for unsealed coding | `ObjectConsistency.unsealedConsistencySentence`; the internal sealed/unsealed proof-certificate bridge remains open |
| Internal universal closure, bounds and sealing | Lean checked | `ObjectCodeClosure`, `ObjectCodeBound`, `ObjectCodeSeal`: nonstandard-input totality, functionality, exact syntax quotation and actual ZFC proofs |
| Sealed internal consistency target | Lean checked sentence and semantics | `ObjectCodeSeal.consistencySentence` quotes actual `ZFCax_s` axioms; equivalence to the internal polynomial remains open |
| Fifteen-positive local short-equation checkpoints | Preserved | 69 operations/degree111,73/80,75/68,76/64; current size-only comparisons across domains and tuples are in SIZE_REDUCTION.md |

## Validation environment

During synchronization, `origin/main` added eight wave-6 packages beside
wave 5. The source material remains in the new research directory. Their
entry-point claims include nine-positive degree 129,875,980 / 788 operations
([45](con-zfc-diophantine-forms/45-multioutput/README.md)), ten-integer degree
237,520,456 / 782 operations
([40](con-zfc-diophantine-forms/40-packing10/README.md)), and an eleven-positive
family ([38](con-zfc-diophantine-forms/38-batching11/README.md)). These delivered
mathematical reductions still distinguish their finite checks from a new
end-to-end Lean theorem. Their coefficient tuples are separate bindings;
the current local P67/P69/P73/P75 proofs retain their prescribed package-36
tuple. A smaller generic coding stage can be investigated after the concrete
program-data bridge is closed.

The checkout uses Lean `v4.32.0` and Mathlib `v4.32.0`. A standard Lake build
of the ZFC endpoint and short-equation modules has completed successfully,
reusing matching Mathlib dependencies. The new modules also have independent
axiom checks; completed audits use only `propext`, `Classical.choice`, and
`Quot.sound`.

## Checked local simplification

`Lean/DiophantineConsistency/ShortEquation.lean` compiles under Lean 4.32.0.
`Lean/checks/ShortEquationAxioms.lean` reports only `propext`,
`Classical.choice`, and `Quot.sound` for its main equivalence. The ring
identity uses only `propext` and `Quot.sound`.

The theorem proves cancellation of the nonzero discriminant and reduction
of the auxiliary coefficient. Its crucial premise is proved modulo 4:
`f² - ((a+2)²-1)t² ≠ -1`. An integer product equal to 1 therefore forces
this factor to be +1, which justifies the coefficient replacement in both
directions. This is an equality of complete zero sets, not a comparison of
sample evaluations.

It supports a candidate 69-operation, degree-111 evaluator of the inherited
15-positive-variable equation. The initial 68-operation estimate missed
the old evaluator's shared multiplication `Δ*f²`; the corrected ledger was
emitted and checked independently. Compiler correctness and its connection to
ZFC have not been inferred from this local theorem.

`ShortSystem.lean` and `ShortFrontier.lean` now also check the 75-operation,
degree-68 and 73-operation, degree-80 alternatives. Both retain exactly the
complete positive zero set of P67. The Lean certificates include their
actual polynomials, literal evaluator identities, and degree upper bounds.
Independent finite audits establish the exact degrees, operation ledgers,
and nonzero leading coefficients. See [SHORT_SYSTEM.md](SHORT_SYSTEM.md)
and [SHORT_FRONTIER.md](SHORT_FRONTIER.md).

The literal circuit and finite ledger have now been emitted and independently
checked: 69 live binary gates, 40 multiplications, 15 additions, 14
subtractions, 15 positive witnesses, and exact degree 111. The selected
nonzero degree-111 monomial has coefficient `8*beta^64`. `ShortCircuit.lean`
includes the actual circuit evaluator, its integer multivariate polynomial,
the evaluation bridge, and equality of its complete positive zero set with
the literal P67 baseline. See [SHORT_EQUATION.md](SHORT_EQUATION.md).

## Exact refutation semidecider

`Computability.lean` shows each arithmetic operation of `EnumPerm.enumStep`
primitive recursive, proves its bounded iteration primitive recursive, and
searches for its first halting bound. `Bridge.lean` composes the existing
calculus-to-ZF and ZF-to-ZFC refutation equivalences. The resulting set
`zfcRefutationInputs` is the constant predicate
`BProv ZFCax_s [] Form.fBot`; its RE proof uses the literal enumerator.

Both new modules compile cleanly. Axiom audits of `refutationInputs_re`,
`halts_iff_refutation`, and `zfcRefutationInputs_re` list only `propext`,
`Classical.choice`, and `Quot.sound`. No consistency assumption is used.

## Checked external consistency equivalences

`Polynomial.lean` fixes the ordinary Jones input to 1 and proves that this
specialization does not raise total degree. `ZFC.lean` now composes this
with the actual refutation semidecider. It provides:

* `zfcNinePolynomial : MvPolynomial (Fin 9) ℤ`, with a natural zero iff
  `BProv ZFCax_s [] Form.fBot`;
* `zfcQuarticPolynomial : MvPolynomial (Fin 58) ℤ`, with total degree at
  most four and the same solvability equivalence;
* the negated equivalences to the syntactic `ConZFC` definition.

These modules and the umbrella import compile cleanly under `lake env lean`.
Both consolidated audit files pass and list no axiom beyond `propext`,
`Classical.choice`, and `Quot.sound`. This is a checked external Lean
equivalence about ZFC's actual syntax. The object-language ZFC derivation
remains open. The separate explicit route
has now closed the coefficient-recipe obligation: see
[EXPLICIT_EQUATION.md](EXPLICIT_EQUATION.md) and [DIRECT_PROGRAM.md](DIRECT_PROGRAM.md).
Its enormous numerical coefficient payload has not been materialized.


The [twelve-integer interpolation review](PROPOSAL_REVIEW_TWELVE_INTERPOLATION.md)
accepts248 operations/degree4832 and223/16000. A compatible auxiliary
Pell witness realizes every requested class after its strong pair is fixed.
The trace companion improves13-integer195/1072 to190/1072. Both full
release modes, all whole coefficient bytes and root's separate ordinary
review pass. The [congruence family](reviews/congruence-certificates-peer.md)
also adds14-integer148/414 and16-integer118/124 tradeoffs. Free positive J
reduces13-positive90/51 to88/51; that preserved page retains90/51. The
ten-positive proposal now passes review; its identical shared-product
sibling reaches123/816 and a further reused alias reaches122/816. The
canonical page now displays the further quadratic10-positive105/408 version.


The latest accepted reductions are9-positive419/1472168 and compact427/1626248
(position-zero encoding plus an identical norm),10-positive105/408 (quadratic
projection and symmetric three-root norm),12-integer208/2400 or202/2912 (fixed-prime separation), and
13-integer184/1072 (identical shared norms). Complete ordinary reviews and
normal/optimized scoped checks pass. The [new direct source](PROPOSAL_REVIEW_QUARTICS407888.md)
yields407 naturals or888 integers, with a917-integer lower-height alternative.
The [projected factorial-radius composition](candidates/projected-factorial-radius/README.md)
now reaches399 naturals, and its
[mixed-domain projection](candidates/projected-radius-mixed-projections/README.md) reaches706
integers, with a735-integer lower-height alternative. The ten-positive
page has passed independent review and become the canonical display.
The previous13-positive90/51 page is preserved.


The [valuation shared-norm packet](candidates/valuation-shared-norms/README.md)
now freezes12-integer208/2400 and202/2912. Seven exact cut identities and
an every-node proof preserve the entire polynomials. A separate graded-lex
calculation over all six formal ports certifies the actual child leading
terms and their nonzero beta-only specialization. Both full candidate
modes and root's independent review pass.

The [projected factorial-radius family](candidates/projected-factorial-radius/README.md)
now reaches399 naturals/317 rows/8286 terms/height83843274, with complete
402/403/453-variable alternatives. The summed radix bounds both factorial
binomials even when the proposed t! output is initially zero. The paired
factorial inequality supplies the strict remaining low-digit bound before
the product formula is used. All six literal quartics, raw exports and
rational SOS restorations pass normal/optimized checks and root review.
A new integer guard/projection family is being checked separately; its
unsealed counts are not yet table entries. Lean remains paused.


The projected-radius integer conversion now passes root ordinary review,
both full candidate modes and deterministic comparisons:862/863/865-variable
quartics plus the891-variable lower-height alternative. Its fresh sign
certificate proves all667 original signs from161 guards before interpreting
arithmetic. Complete reverse projection retains every guard. These improve
the888/917 checkpoints as recorded in the comparison; no semantic sign
relaxation beyond the literal row certificate is included in these counts.


The [identical integer14 simplification](candidates/constructive-integer14-shared/README.md)
reduces147 to145 live operations at unchanged degree568. Two complete
`(1+x)-1=x` substitutions preserve the entire polynomial and all six
fixed coefficients. Root reviewed the literal checker, all node maps,
normal/optimized replays and all30 sealed files. The lower-degree
148/414 and lower-cost137/792 alternatives remain useful tradeoffs.
The then-current10-positive105/408 PDF and TeX are unchanged by this minor
integer-domain simplification; Lean remains paused.


The [mixed retained-wire family](candidates/projected-radius-mixed-retained/README.md)
now gives1,580/933/788/724/710 unrestricted integer variables, all at
exact degree4. It keeps all original raw rows and coefficients, proves
A and D nonnegative from four original-row bounds, and copies107 guard
triples into the literal reviewed994 equation, with six fresh Legendre
witnesses for its two remaining guards. The full592-wire map is over
integers. All five collected quartics and complete signed inverses pass
independent and deterministic checks in both Python modes. Heights remain
427/4,750/737,653/737,653/938,261; each matched159-guard sibling loses
156 coordinates,52 rows and780 terms. The smaller706-variable, larger-height
family remains a separate tradeoff. The canonical PDF/TeX and Lean are unchanged.


The [signed main-root reduction](candidates/constructive-integer14-quadratic/README.md)
now reaches14 unrestricted integer variables,121 operations and exact
degree312. Absolute-value Pell folding recovers the missing main norm
before the signed rank bootstrap; a whole-product absolute height bound
resolves the quadratic projection for both signs of H. Explicit integer
n maps preserve zero existence in both directions. The complete proof,
all six original coefficients, universal formula binding, literal35-term
norm, exact leading form and normal/optimized replays pass independent
and root review. This improves both cost and degree over14-integer
137/792,145/568 and148/414, which remain preserved checkpoints. It has
more variables and operations than the then-current10-positive105/408 page,
so that complete PDF/TeX remains the canonical display. Lean is paused.


The [contracted mixed-bound family](candidates/projected-radius-mixed-bounds/README.md)
now reaches988/729/703/701/700 unrestricted integer variables at degree4.
All585 original body rows are unchanged. Restoring592 raw wires over
integers licenses the four actual t,n,A,D row bounds;107 copied guard
triples plus six fresh A/D witnesses give the literal reviewed994 zero.
Every projection restores the entire988 parent first. Independent and
full deterministic normal/optimized checks pass all1177 row identities,
complete coefficients/inverses and15 corruption controls. The700-variable
polynomial has10,437 terms and height2,445,790,974,704;729 retains lower
height63,905,891. Each matched994/735/709/707/706 checkpoint loses six
variables, two rows and28 terms. The710-variable retained-wire option
has much smaller height938,261. Canonical PDF/TeX and Lean are unchanged.


Two [identical prefix rewrites](candidates/constructive-integer14-quadratic-shared/README.md)
reduce the new14-integer degree312 equation from121 to119 operations.
Reusing q² and factoring ell(ell+1)k²=(ell*k)(ell*k+k) preserve the entire
polynomial over every commutative ring. Complete148-to146 node coverage,
all removed private definitions, every named register, the full35-term
norm and all six payloads pass independent root review and both complete
checker/rebuild modes. All33 packet seals pass. The signed ordinary proof
and exact nonzero leading coefficient transfer unchanged. This is a minor
saving within the new signed degree312 route; the canonical10-positive
105/408 PDF/TeX remains the separate lower-variable/operation display.
Lean remains paused.


The [thirteen-integer quadratic trace equation](candidates/integer13-quadratic-trace/README.md)
now uses135 operations at exact degree536, down from184/1072. Normalized
trace gives both CRT congruences before signs, the unscaled guard gives
four-root separation, and signed Pell folding restores the main norm.
The whole-product height proof resolves its quadratic projection, then
explicit unrestricted n maps restore the frozen trace endpoint in both
directions. Root reviewed the entire ordinary proof and independent
literal checker; all four normal/optimized checker/rebuild commands pass,
including the full495-term norm, centered425-term degree calculation,
authentic six ports and all138 original archive members. This improves
both current13-integer cost and degree. At that checkpoint, the10-positive105/408 page remained
a separate lower-variable/operation display. Lean is paused.


The [five exact original-row sign consequences](research/guard-seed-consequences/README.md)
remove two factorial-output guards, the moduli-product and CRT quotient
guards, and one endpoint quotient guard before any arithmetic semantics.
The CRT numerator uses its independently proved defining sums, avoiding
a circular quotient dependency. The [complete102-guard family](candidates/projected-radius-mixed-signs/README.md)
now gives973/714/688/686/685 integer variables, all degree4. A literal
102-triple transfer plus15 new Legendre witnesses restores the full988
parent; all integer projections are reversed first. Root reviewed both
ordinary proofs and independent checkers. Full normal/optimized checks
and rebuilds pass every original-row identity, the975-step sign ledger,
all coefficients and inverses. Each matched988/729/703/701/700 parent loses
15 variables, five rows and73 collected terms at unchanged height. The
smaller-coefficient retained710 family and canonical PDF/TeX are preserved;
Lean remains paused.


The [scalar-carrier twelve-integer equations](candidates/scalar-carrier12/README.md)
now use145 operations/degree1200 and141/1456, improving208/2400 and202/2912
with the same twelve unrestricted variables and all six original constants.
A scalar intersective quintic enforces H|K and excludes zero strong scale;
prime-order separation leaves four roots, and signed folding recovers the
missing main norm before its whole-product projection. The completeness
proof keeps one strong witness fixed while selecting the translated
intersective residue. Direct nonodd step-down is proved from the auxiliary
index polynomial. Full independent ordinary review, separate all-register
ring binding, all495 norm coefficients, exact every-gate leading induction,
whole payloads/parent inventory and final normal/optimized checks pass.
Both degrees are halved; cost falls by63 and61 operations. Canonical
10-positive105/408 PDF/TeX remains the lower-variable/operation tradeoff;
Lean stays paused.


The [nine-positive folded-saturation equations](research/nine-folded-saturation/README.md)
now reach414 operations/degree1,355,142 on the full original31 tuple and
422/1,497,238 on compact54-sharp. Saturating the strong norm with the
first Pell radicand allows a two-root equation; coprimality recovers both
squares, then main-Pell folding recovers C=psi_A(B1). Positivity is proved
before extraction, and finite matrix periods construct positive i,j,n.
Both directions retain the exact source/binomial boundary and whole fixed
tuples. Root read the full ordinary proof/checker and verified every
retained source node, every local algebraic cut, centered identity and
actual-coefficient homogeneous witness in both Python modes; both complete
rebuilds pass and all packet seals are checked. Both cost and degree improve
the matched419/427 parents. Lower-degree higher-cost alternatives remain
separate, and canonical10-positive105/408 PDF/TeX is unchanged. Lean is paused.


Two [exact private sign orbits](research/guard-sign-orbits/README.md)
now replace the U and bootstrap-witness guards. Complete raw/contracted
row identities negate U and its sixteen quotient partners together, or
reflect Zminus1 with its two private wires. The independent A>=2 row
bound excludes Z=0 before reflection; U=0 uses the identity branch.
All100 remaining guard values and all643 semantic-prefix coordinates
stay fixed. The [whole100-guard family](candidates/projected-radius-mixed-orbits/README.md)
has967/708/682/680/679 integer variables at degree4. Normalize private
values first, then six fresh witnesses give the literal973 equation;
reverse all signed projections before that step. Root reviewed the full
proofs/checkers and all normal/optimized checks/rebuilds pass. The679
polynomial has397 rows and10,335 terms at unchanged height2,445,790,974,704.
Each matched973/714/688/686/685 checkpoint loses six variables and two
rows. The retained-wire low-height family and canonical PDF/TeX remain
separate tradeoffs. Lean stays paused.

## Tightened nine-positive folding accepted

The [tightened packet](research/nine-folded-saturation-tight/README.md)
now gives409 operations / degree1,191,572 on the whole original31 tuple
and417 /1,316,548 on the separate compact54-sharp tuple. It improves the
frozen414/422-operation equations in both operation count and degree.
The strong ordinate omits J, the auxiliary quotient uses positive j
without a shift, the carrier is Jn+Q, and the first norm shares its
majorant. A new strict-gap proof forces positive margin before root
extraction; two finite matrix periods and a strict carrier bound construct
all three changed positive witnesses. No tuple or domain is weakened.
The [root review](reviews/nine-folded-tight-root-peer.md) records the full
ordinary proof audit, exact degree argument, all four normal/optimized
checks and rebuilds, and closed artifact seals. This nine-variable result
is a separate tradeoff from the maintained ten-positive one-page equation.
Lean remains paused; no new internal-ZFC endpoint is claimed.

## Direct positive J in the ten-variable equation accepted

The [free-J ten-positive equation](candidates/ten-positive-free-j/README.md)
saves two operations, reaching103 at the same exact degree408 and ten
positive unknowns. The enlarged positive J domain is sound: odd main
index recovery gives p=R before q parity, then odd q would force even J
and even R. Coprimality is used only after this contradiction recovers
even q. The J=1 case constructs fresh positive source61 witnesses and
uses its actual unrestricted-positive-J soundness statement. The whole
original tuple and separately calibrated BFS tuple remain distinguished.
The [root review](reviews/ten-positive-free-j-root-peer.md) and
[independent ordinary review](reviews/ten-positive-free-j-ordinary-peer.md)
record the proof and full literal affine-map/degree checks. All four
normal/optimized checks and deterministic rebuilds passed. This minor
two-operation saving does not trigger a new canonical PDF/TeX rendering;
its complete105-operation page remains available pending a substantial
improvement. Lean remains paused.

## Raw100-guard low-height quartics accepted

The [retained-wire100-guard packet](candidates/retained-radius-mixed-orbits/README.md)
gives complete integer quartics in1559/912/767/703/689 unknowns, at
coefficient heights427/4750/737653/737653/938261. Each saves21 unknowns
and seven quadratic rows over its corresponding frozen107-guard raw
parent, without increasing height. All original raw coefficients remain.
An exact zero-set bijection restores592 triangular monic affine wires
and copies all100 guard triples to the actual frozen967 equation before
using its sign theorem; no fresh witness or sign premise is needed for
the bridge. Each signed projection first restores the whole raw parent.
The [root review](reviews/retained-orbits-root-peer.md) records all1277
row identities, complete coefficient collections, four successful
normal/optimized checks/rebuilds and closed seals. The contracted679
quartic remains a different coefficient-height tradeoff. No new Lean
endpoint is claimed and formalization remains paused.

## Smaller signed fourteen-variable guard accepted

The [guard-reduced equation](candidates/constructive-integer14-guard-reduced/README.md)
has14 unrestricted integer unknowns,117 operations and exact degree312.
It removes the explicit v-square factor from the guard. Its new proof
excludes v=0 by rationalizing the remaining two roots and deriving an
impossible CRT divisibility, before using any weak-scale estimate. Both
integer witness maps regenerate only the four private guard coordinates;
the entire degree256 norm and six fixed coefficients are unchanged.
The full output difference has degree at most304, so the complete
nonzero degree312 leading component survives. The
[root review](reviews/integer14-guard-root-peer.md) records all node/guard/
norm identities, four successful normal/optimized checks and rebuilds,
and closed seals. The [initial research note](reviews/signed14-guard-research.md)
also records why two tempting smaller positivity gadgets fail. Lean and
the canonical ten-positive page remain unchanged.

## Ten-positive102/388 accepted

The [shifted strong equation](candidates/ten-positive-shifted-strong/README.md)
now reaches102 operations and exact degree388 in ten positive unknowns.
It uses I=(i+q²)c² and the shorter transport L=HI+b. The shift preserves
the unconditional lower bound and square-ordinate divisibility; a new
rational-rho bound licenses the smaller transport before parity recovery.
Canonical completeness keeps the strong ordinate and constructs a fresh
positive final n, including zero transport quotient. The complete norm
has a nonzero selected coefficient2^28*beta^224 in degree388. The
[root review](reviews/shifted-strong10-root-peer.md) and
[independent ordinary peer](reviews/ten-positive-shifted-strong-ordinary-peer.md)
record the full proof, exact gate/degree/whole-tuple checks, four passing
normal/optimized replays and closed seals. A new complete one-page display
is being prepared for the combined gain over105/408; its predecessor
will be preserved. Lean remains paused.

## Canonical page updated to102/388

The maintained [equation.pdf](equation.pdf) and standalone
[equation.tex](equation.tex) at that checkpoint printed the complete ten-positive102-operation,
exact-degree388 equation, including every fixed constant, on one Letter
page. This batches the direct-J, shifted-strong and shorter-transport
improvements into one update over the preserved105/408 page: three fewer
operations and degree20 lower. The complete436-character seed,62-character
alphabet,943 tiles and closed arithmetic coefficient recipe are unchanged.
The [new page packet](candidates/one-page-shifted10/README.md),
[independent root page review](reviews/shifted10-page-peer.md) and
[CURRENT_EQUATION.json](CURRENT_EQUATION.json) bind the displayed bytes.
Both independent peer modes, renderer replays and full coefficient
reconstruction modes pass; the page was visually reviewed. The previous
[105/408 PDF](candidates/one-page-quadratic10/equation.pdf) and its TeX
remain preserved. Lean formalization remains paused.

## Twenty-one pointwise guard consequences accepted

The [main-root/modulus proof](research/main-root-and-modulus-signs/README.md)
recovers15 main-root signs and six power-modulus signs from the unchanged
raw equations with79 retained guards. Its independent semantic-prefix
proof precedes a strict A>W^W bound, signed-index recovery and negative-root
residue contradiction. Only then does a positive-base power call establish
f0>0 and the final modulus sign. All15 actual exponents are proved positive.
The [root review](reviews/main-root-signs-root-peer.md) and
[independent peer](reviews/main-root-modulus-signs-peer.md) verify the
complete original-row, constructor and21-call ledger; all six root
normal/optimized checks, rebuilds and peer runs pass. At the same body
tuple,79 existing triples and63 fresh Legendre witnesses reach the literal
frozen967 equation. Complete new quartics and signed projections are being
materialized separately; no unverified projected count is added here.
Lean and the current canonical PDF/TeX remain unchanged.

## Fixed root weight lowers ten-positive degree to368

The [weighted-root equation](candidates/ten-positive-weighted-roots/README.md)
has ten positive unknowns,102 operations and exact degree368. It replaces
the full-mu strong shift by I=i*c² and weights only the first root by3.
All signed cancellations are excluded before root extraction: two pairs
would imply mu|8, the third would equate an integer to -1/Delta, and a
zero triple would imply mu|2025, then mu|25 despite mu>=1025. Main folding
then gives the strict bound needed for weighted transport. Canonical
completeness uses the explicit positive shifts i_new=i_old+q² and
n_new=n_old+2*tau. The [root review](reviews/weighted10-root-peer.md) and
[independent ordinary peer](reviews/ten-positive-weighted-roots-ordinary-peer.md)
record the full proof and exact circuit/degree/whole-tuple checks. All four
normal/optimized checks and rebuilds pass; the unique leading component
has a positive selected coefficient2^28*beta^184. The prior102/388 packet
is preserved; a complete new page is under review. Lean remains paused.

## Complete79-guard compact quartics accepted

The [materialized compact family](candidates/projected-radius-main-root-signs/README.md)
gives full integer quartics in904/645/619/617/616 variables. The smallest
has376 quadratic rows,10,028 collected terms and coefficient height
2,445,790,974,704; the645-variable point has5,580 terms and height63,905,891.
Every profile saves63 unknowns and21 rows over its matching100-guard
parent at unchanged height. Complete signed inverses first restore all79
guards, then592 raw affine wires. The ordered21-sign theorem supplies
63 fresh witnesses at unchanged body values into the literal967 equation.
The [root review](reviews/main-root-quartics-root-peer.md) records full
coefficient collections, every100 copied/fresh guard-row identity, all
four passing normal/optimized checker/rebuild replays and closed seals.
These are checked whole equations, not estimates from deleting guards.
Lean and the ten-positive display remain separate and unchanged.

## Retained-coefficient79-guard quartics accepted

The [new raw family](candidates/retained-radius-main-root-signs/README.md)
keeps all original coefficients and gives1496/849/704/640/626 integer
variables, with exact degree4 and heights427/4750/737653/737653/938261.
The smallest has386 rows and8,904 collected terms. Each profile saves
63 variables and21 rows at unchanged height against its100-guard parent.
The [root review](reviews/main-root-raw-quartics-root-peer.md) records
the complete1256-row integer bijection into904, all592 affine inverses,
and the composed79-copied/63-fresh-witness transfer into literal967.
All100 target guard rows and every full collected polynomial are checked.
All four root normal/optimized checker/rebuild replays and closed seals
pass. The616-variable compact quartic is a separate height tradeoff;
no new Lean or native calibration endpoint is claimed.

## Comparison-base positivity guard removed existentially

The [comparison-base proof](research/comparison-base-sign/README.md) permits
negative B and then lifts it to a positive comparison base while preserving
all78 other guard values. Its complete1177-row audit accounts for62 private
coordinates,141 unit gates and every46 affected nongate constraints. The
signed-index and21-sign proofs precede the lift; q4 positivity is supplied
at the new tuple, not asserted at the old tuple. Three fresh Legendre
witnesses reach the literal904 source. The [root review](reviews/comparison-base-sign-root-peer.md)
and [independent peer](reviews/comparison-base-sign-peer.md) record full
normal/optimized author and peer replays, all passing. New compact/raw
quartics are being materialized separately; this theorem alone supplies no
new projected coefficient count. Lean remains paused.

## Positive short projector reaches101 operations at degree368

The [short-projector equation](candidates/ten-positive-short-projection/README.md)
uses ten positive unknowns and101 live operations at exact degree368.
Kpos=X(3c-2X)+2 is positive after main folding and obeys
Kpos=H*X*c-2*Kquad. Only2 is cancelled modulo odd H; P is retained in
the whole-product argument. Every old positive zero maps to a new one
by the strictly positive shift n_new=n_old+3*(Kquad/H)-X*c. The
[root review](reviews/short10-root-peer.md) and [independent ordinary peer](reviews/ten-positive-short-projection-ordinary-peer.md)
check the full unbounded proof. All four root normal/optimized checker
and rebuild replays, complete53-entry seals and full coefficient binding
pass. The entire polynomial change has degree at most360, preserving the
degree368 leading component. A complete one-page specification is being
reviewed for the next canonical PDF/TeX update. Lean remains paused.

## Canonical complete page updated to101/368

[equation.pdf](equation.pdf) and committed standalone [equation.tex](equation.tex)
now print ten positive unknowns,101 operations and exact degree368. This
batches the fixed root weight and positive short projector: one operation
and20 degrees below the preceding canonical102/388 page, with the entire
constant recipe unchanged. The [complete new page](candidates/one-page-short10/README.md)
includes all436 seed characters,62-symbol alphabet and943 tiles. The
[independent root page review](reviews/short10-page-peer.md) binds all101
live gates universally, verifies all four full ports, and records passing
normal/optimized page peers, renderer replays, author reconstructions and
27 closed seals. The full rendered page was visually checked. All prior
pages remain preserved; [CURRENT_EQUATION.json](CURRENT_EQUATION.json)
binds the exact canonical PDF, TeX and polynomial. Lean remains paused.

## Complete78-guard compact quartics accepted

The [new compact family](candidates/projected-radius-comparison-base/README.md)
has901/642/616/614/613 integer unknowns, all at exact degree4. The613
profile has375 rows,10,013 terms and coefficient height2,445,790,974,704;
the642 profile has5,565 terms at height63,905,891. Each saves three
unknowns, one row and15 terms at unchanged height against its matching
79-guard predecessor. The [root review](reviews/comparison-base-quartics-root-peer.md)
checks every full coefficient collection and inverse. Complete projection
restoration precedes the signed-B theorem and62-coordinate comparison lift;
all78 guard values stay fixed, while three fresh witnesses guard NEWq4
in literal904. Its21-sign theorem then reaches967. All four root
normal/optimized checker/rebuild replays, nested complete source checks
and34 closed seals pass. The canonical101/368 page and Lean remain unchanged.

## Complete78-guard low-height quartics and independent family peer

The [retained-coefficient family](candidates/retained-radius-comparison-base/README.md)
has1493/846/701/637/623 integer variables at exact degree4, with
heights427/4750/737653/737653/938261. The623 profile has385 rows and
8,889 terms; it saves three variables and one row at unchanged height
against626. The [root review](reviews/comparison-base-raw-quartics-root-peer.md)
records every1255 raw/guard row and901 restriction identity in the exact
1493↔901 integer bijection. Only after complete restoration does the
nonpointwise comparison lift reach904 with fresh NEWq4 witnesses, then967.
All four root normal/optimized checker/rebuild runs and35 closed seals pass.
The [separate family peer](reviews/comparison-base-families-peer.md) independently
checks all ten compact/raw inverse certificates, all raw/guard identities
and62 snapshot recipes. Both focused root replays reproduce its final
receipts and reject nine corruptions. The compact613 family is a separate
height tradeoff. Canonical101/368 PDF/TeX and paused Lean remain unchanged.

## Literal constructor prose correction

The [constructor erratum](reviews/main-root-constructors-erratum.md) corrects
two aliases in the frozen21-sign note: raw36=y+1>=1, and
raw86=(t+x+y+M0+2)^(2^23)>=3. Root checked every cited original row.
The431-step constructor certificate already uses those correct literal
rows, so all exponent-positivity, guard and equation conclusions remain
unchanged. Neither constructor has fixed parity from these premises.
Frozen certificates and polynomials are preserved; subsequent proofs use
the corrected descriptions. Lean remains paused.

## Direct positive X and zero-offset research

The [direct-base research](research/ten-positive-direct-base/README.md)
replaces X=wq by X=q+x and adds a delayed divisibility carrier. Its
complete prototype has ten positive unknowns,107 operations and degree340.
The [ordinary peer](reviews/ten-positive-direct-base-ordinary-peer.md)
checks the unbounded proof and a separate complete free-ring center cut:
remove the H denominator after whole-product projection, then recover q|X,
then justify X/q⁴ as an integer. Full materialized-candidate verification
is underway; this research checkpoint alone adds no accepted frontier.
The [zero-offset draft](research/ten-positive-zero-offset/PROOF.md) proposes
removing the inner constant offset in the scaled main base. Its stronger
ratio estimate suggests one fewer operation at unchanged degree; independent
review and literal checks are pending. The canonical101/368 page and
paused Lean remain unchanged.

## Complete direct-base107/340 endpoint accepted

The [direct-base candidate](candidates/ten-positive-direct-base/README.md)
has ten positive unknowns,107 live operations and exact degree340. It
replaces X=wq by X=q+x and recovers q divisibility from a new carrier
after the whole-product projection removes H. The [root review](reviews/direct107-root-peer.md)
and [ordinary peer](reviews/ten-positive-direct-base-ordinary-peer.md)
verify the complete proof chronology and positive witness map. All four
root normal/optimized checks and rebuilds pass, with61 closed seals,
full four-port binding, universal center/norm identities and an attained
nonzero degree340 coefficient. This lowers degree by28 at six extra
operations relative to101/368. The cheaper complete canonical page stays
unchanged; no global optimum or new Lean endpoint is claimed.

## Bootstrap guard exchange accepted; coefficient benefit still being measured

The [guard-exchange proof](research/bootstrap-guard-exchange/README.md)
replaces base0.T's sign guard by the bootstrap Zminus1 guard, keeping78
guards. Signed-A/B index recovery and four actual source calls exclude
negative A without assuming raw86 even or interpreting a factorial early.
The converse changes one free bootstrap coordinate, six gates and one
constraint. The [root review](reviews/bootstrap-guard-exchange-root-peer.md)
and [independent peer](reviews/bootstrap-guard-exchange-peer.md) check
both whole-source existence maps. Both root author/peer normal/optimized
runs reproduce the final receipts, and all four research seals pass.
Actual coefficient profiling is separate; no new projected count follows
from the exchange alone. The [paired-index proposal](research/paired-index-guards/README.md)
is another unfinished lead, with its exact local factorial/binomial
obligation recorded. Canonical101/368 PDF/TeX and paused Lean are unchanged.

## Complete ten-positive99/368 endpoint accepted

The [zero-offset equation](candidates/ten-positive-zero-offset/README.md)
uses ten positive unknowns,99 live operations and exact degree368. The
stronger directly proved ratio bound permits A=mu*a+1; sharing the
already-needed muY product in A-1=(muY)(X+1) removes a second operation.
The [root review](reviews/zero99-root-peer.md) and [independent ordinary peer](reviews/ten-positive-zero-offset-ordinary-peer.md)
check full fresh canonical completeness, including positive auxiliary T
and final n, and every soundness license. All four root normal/optimized
literal checker/rebuild replays, both focused peer modes and62 closed
seals pass. Complete coefficient payloads, all99 live definitions and the
attained degree368 leading component are bound. This improves101/368 by
two operations. The complete canonical101/368 PDF/TeX is preserved while
minor presentation updates are batched, as requested. Lean stays paused.

## Guard-exchange profile finds no benefit in the tested configurations

The [paired coefficient profile](research/bootstrap-guard-exchange-profile/README.md)
tests both compact/raw sources at five support caps, keeping every setting
and source coefficient except the guarded value fixed within each pair.
All20 profiles in each root normal/optimized replay reproduce the complete
receipts. Integer substitutions verify and every quartic is independently
expanded. The [root review](reviews/bootstrap-profile-root-peer.md) records
unchanged variable/row/support/height metrics and one added term in each
projected exchange. The accepted guard placement is retained. An unrelated
raw baseline order gives a possible613-variable/9661-term point at the
same high coefficient height; a full separate package is under review.
No new accepted frontier follows from this research measurement alone.
Canonical101/368 PDF/TeX and paused Lean remain unchanged.

## Default-affine raw613 support improvement accepted

The complete [raw/default-affine613 quartic](candidates/retained-radius-default-affine/README.md)
reduces the expanded support from10,013 to9,661 monomials at the same
613 integer variables,375 quadratic rows, degree4 and coefficient height
2,445,790,974,704. The exact unchanged1493 input uses support8 for both
affine and quadratic restorations. All880 integer restorations and all
9,661 coefficients were independently replayed in normal and optimized
Python, along with both deterministic rebuilds; see the
[root review](reviews/default-affine613-root-peer.md). All78 original
guards remain. This is a new projection configuration, separate from the
bootstrap guard exchange. The canonical one-page equation remains unchanged.
