# Exclusion audit for additional Lean proof simplification proposals

> **Freshness update:** the final exclusion cutoff is `7def5e00ef3593b296eb595add1d955d27121d0c`. See `FRESHNESS.md` and `freshness-exclusions.json` for four added packets and fifteen additional coverage records. Integer interval induction and shared-edge construction below are now explicitly withdrawn.

## Scope and interpretation

Review snapshot: `553a5f7a463cbaab8800ff8148fef0bc5a9e1b22` (26 October 2026). The complete requested on-disk corpus was inventoried: six placed packets (323 files) plus all twelve incoming ZIPs (2,405 members, 2,084 textual members extracted). The incoming README and ADOPTION.md were also inspected for relevant scope and placement. Nested copies of older packets and unchanged production snapshots are evidence, not independent new recommendations.

This is a mechanism-level exclusion screen. All prior proposals are treated as already applied, including notes-only, optional, uncompiled, deferred and rejected-default ideas. Merely validating one now, renaming its abstraction or adding another announced client is not new. A proposal must remove a different proof obligation or add a materially different invariant.

The review used main manuscript proposal sections and section indexes, supplementary technical notes, earlier detailed exclusion catalogs cross-checked against the actual placed manuscripts, proposed-code/patch inventories, and candidate-specific full-text searches. It does not claim a fresh semantic proof review of every bundled implementation, nor a traversal of every remotely linked historical manuscript in the long incoming index. The scope is the actual requested directories at the pinned snapshot. No global mathematical originality is claimed.

`EX001`–`EX075` retain the useful 75-family classification from the earlier Round2 packet, with its report-key references remapped below; their inherited wording is attributed to that packet. `L01` onward records later incoming refinements and notes-only directions. Coverage entries overlap and must not be counted as independent mathematical ideas.

## Exact source key

All P- paths are repository files. All I- archives are under `docs/incoming/`; the second path is an exact member or section directory. `report-section-index.json` records SHA-256 and every section heading/line.

| Key | Repository path or archive | Main manuscript member |
| --- | --- | --- |
| P-a | `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26a/report.tex` | Repository file |
| P-b | `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26b/report.tex` | Repository file |
| P-c | `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26c/report.tex` | Repository file |
| P-d | `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26d/report.tex` | Repository file |
| P-e | `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26e/report/report.tex` | Repository file |
| P-f | `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26f/report/sections/` | Repository file |
| I-deltas | `docs/incoming/Lean_Proof_Simplification_New_Deltas_2026-10-26.zip` | `Lean_Proof_Simplification_New_Deltas/report/report.tex` |
| I-round2 | `docs/incoming/ProveIt_Lean_Simplification_Round2_2026-10-26.zip` | `LeanReview2/report/sections/` |
| I-additional | `docs/incoming/additional_lean_simplifications_2026-10-26.zip` | `additional_lean_simplifications_2026-10-26/report/additional_lean_simplifications.tex` |
| I-eight | `docs/incoming/diophantine-lean-additional-simplifications-2026-10-26.zip` | `diophantine-lean-additional-simplifications-2026-10-26/report.tex` |
| I-directions | `docs/incoming/diophantine-lean-new-directions-2026-10-26.zip` | `new-lean-simplification-2026-10-26/report.tex` |
| I-ideas | `docs/incoming/diophantine-lean-new-ideas-2026-10-26.zip` | `diophantine-lean-new-ideas-2026-10-26/report.tex` |
| I-six | `docs/incoming/diophantine-lean-new-simplifications-2026-10-26.zip` | `diophantine-lean-new-simplifications-2026-10-26/report/report.tex` |
| I-roadmap | `docs/incoming/diophantine-lean-post-roadmap-2026-10-26.zip` | `diophantine-lean-post-roadmap-2026-10-26/report/new-proof-simplifications.tex` |
| I-simplification | `docs/incoming/diophantine-lean-simplification-2026-10-26(1).zip` | `diophantine-lean-simplification/report.tex` |
| I-five | `docs/incoming/lean-proof-simplification-new-2026-10-26.zip` | `lean-proof-simplification-new-2026-10-26/report.tex` |
| I-review | `docs/incoming/lean-proof-simplification-review-2026-10-26.zip` | `lean-proof-simplification-review/lean-proof-simplification-review.tex` |
| I-residual | `docs/incoming/lean-simplification-residual-2026-10-26.zip` | `lean-simplification-residual-2026-10-26/report.tex` |

## Earlier six-packet exclusions

Attribution: the first 75 coverage entries are taken from `ProveIt_Lean_Simplification_Round2_2026-10-26.zip::LeanReview2/incoming_audit/EXCLUSION_CATALOG.md`, and cross-checked against current placed reports/notes. They are existing ideas, not new work of this review.

| ID | Existing mechanism and scope | Source evidence |
| --- | --- | --- |
| EX001 | **Seven private optional-list-lookup inductions.** Use List.mem_of_getElem? and List.getElem?_of_mem or mem_iff_getElem? at AnnotatedRename, Bound, ProofChecker, Assumption, RuleSide; wrappers or direct replacement. | P-e:6; P-b:3; P-d:9.2; P-c:3; P-a:3.2. |
| EX002 | **Option map injectivity.** Replace AnnotatedParents judgment-code option case split by Option.map_injective judgmentCode_injective. | P-e:6. |
| EX003 | **Realizer and optimizer recursor congruence.** Eliminate inner Nat.rec induction in PRCode.Realizes.prec, ScalarPRCode.Realizes.prec and ScalarPROptimizer.eval_optimize by explicit simp or shared axiom-free RecursorCore.rec_congr. | P-a:3.1. |
| EX004 | **Assignment naturality.** Shared natAssignment composed with Sum.map and Expr.eval_rename for reindex/conjunction/disjunction/existsBlock; preserve expression fields and counts. | P-b:4.1-4.2; P-d:2; P-c:4; P-a:3.3. |
| EX005 | **Concatenated witness existential.** Generic equivalence between Fin(m+n) witness and two Fin blocks via Fin.addCases, including zero lengths. | P-b:4.1. |
| EX006 | **Early witness-count projections.** Move existing constructor count projection lemmas from RepresentationSize to constructors or lightweight module to avoid unfolding large data. | P-b:4.3. |
| EX007 | **Recursor iteration mechanics.** Share fixed points, zero/done stability, successor-right/left and invariant or reject-or-good laws across five scanners and ContextLookup; keep executable Nat.rec definitions. | P-e:7; P-b:5.2; P-d:5; P-c:9; P-a:8.1. |
| EX008 | **Encoded-step semiconjugacy.** Share typed/encoded iterator fusion and scan-list/table simulation from exact step_cons/terminal/reject laws; includes AnnotatedClosure coding/execution induction. | P-e:7; P-b:5.2; P-c:9; P-a:8.1. |
| EX009 | **Guarded-history fold.** Share run_append, run_sound, Produces.append and Produces.step for Rename/Bound/ProofChecker with distinct Line/Judgment types and emit function. | P-e:8; P-b:5.1; P-c:9.2. |
| EX010 | **Explicit dynamic-seed PR iterator.** Introduce iterateFrom with realized seed/fuel and parameterized step for scanner PR builders; preserve .val program and single expensive validator. | P-b:5.3; P-c:9.3. |
| EX011 | **Exact numeric Boolean reflection.** Derive check=truth valid from 0-or-1 range and check=1 iff valid=true, then simplify Bound/Rename step_cons. | P-e:8; P-b:5.4; P-a:8.2. |
| EX012 | **Common tag threshold dispatcher.** One arithmetic theorem for 0/1,2,3/4/5,6/7 and >=8 outcomes in BoundLocal/RenameLocal, over all natural tags. | P-e:8; P-b:5.4. |
| EX013 | **Carrier finite positivity enumeration.** After fin_cases infer coordinate via hv _ in Carrier66.drop_pos/restore_pos instead of enumerating exact indices. | P-e:3. |
| EX014 | **Carrier canonical zero normalization.** Replace canonical_zero unfold/rw/ring by narrow simp using canonical equalities. | P-e:3. |
| EX015 | **Integer units.** Use Int.eq_one_or_neg_one_of_mul_eq_one in ShortSystem.unit_eq_one and reuse uniformly in product_eq_one_iff with sign exclusions. | P-e:4. |
| EX016 | **Five residual squares.** ShortSystem.residualSum_zero_iff via nonnegative-add/square-zero lemmas or Finset.sum_mul_self_eq_zero_iff rather than repeated nlinarith. | P-e:4; P-f:report/sections/02_local.tex:55-104; P-a:4.1. |
| EX017 | **Common executable residual aggregation.** Share eval_sumExpressions/sumSquares zero iff, degree <=2d and parameterized (b+1)*length cost bound across DAGQuartic, NaturalDAGQuartic, QuadraticRegisterSystem, QuarticCost. | P-b:6.1; P-d:8.1; P-c:10; P-a:4.2. |
| EX018 | **Shared semiring gate induction.** Extract GatesSyntax/data below generic semiring soundness/completeness then derive natural/integer compiler theorems without import cycle. | P-b:6.2; P-d:8.3. |
| EX019 | **Merge identical constructor branches.** QuarticCompiler.Gates.complete add/mul proof alternatives share one branch. | P-e:5. |
| EX020 | **Move syntax degree and rename laws earlier.** Canonical Expr polynomial_rename, syntaxDegree/polynomial_degree_le at expression layer; weighted degree at constant weight one; keep cancellation-aware normal forms. | P-b:6.2; P-d:8.2; P-a:7.2. |
| EX021 | **Generic RHS degree interface.** Share DAGQuartic/NaturalDAGQuartic node RHS degree <=2 from wire degree <=1 and small degree add/sub helpers. | P-e:11. |
| EX022 | **Shorter run_map induction step.** Use map_append/map_singleton/Node.eval_map directly at recursive boundary in ArithmeticDAG.run_map. | P-e:5. |
| EX023 | **Cast Pell conclusion as a whole.** Replace FirstPellCarrier.first_norm_facts_int final disjunction split by exact_mod_cast hgap, retaining lifts and divisibility guards. | P-e:5. |
| EX024 | **Shared DivMod certificate.** One neutral arithmetic certificate_iff for QuadraticDivMod/RegisterDivMod; retain separate realizers and witness counts 1/23. | P-e:6. |
| EX025 | **Identical scalar tail.** Extract SplitNinePolynomial59/GapNinePolynomial66 ratioValue with common map/cast laws and aliases; keep recipe exponents and b factor distinct. | P-e:9; P-c:8. |
| EX026 | **Identical 99-node free-carrier tail.** Common boundary-port block for Split 416..514 and Gap 385..483 under reference renaming; prove embedding and common ratioValue semantics, no copy gates. | P-c:8. |
| EX027 | **Guarded solution transport.** HasSolution(D,P) congruence/composition via two existential directions, not assignment bijection; Current69/70/71 same-domain examples. | P-e:10. |
| EX028 | **Nine-coordinate existence packaging.** Parameterize evaluator to share SplitSourceExistence/GapSourceExistence66 positive/natural coordinate existential proofs; slot7 unshifted internally. | P-f:report/sections/03_architecture.tex:11-67. |
| EX029 | **Named conjunction accessors.** Derived Canonical.Z_eq_delta/index_eq_one/rank_pos and PortBounds/core positivity accessors without changing conjunction definition. | P-f:report/sections/03_architecture.tex:68-98. |
| EX030 | **Coherent restored source and scalar window.** One actual source assignment and positive N yielding both low/high mask tests, shared Carrier65->66 restoration and radix power normalization. | P-f:report/sections/03_architecture.tex:99-146; P-a:source_notes/digits-review.md:8. |
| EX031 | **Base interface below completeness.** CurrentCarrierBase2011 below ThirteenCarrierComplete, old facade retained, simpler digit clients redirected. | P-f:report/sections/03_architecture.tex:147-171. |
| EX032 | **Parameterized Split/Gap degree profile.** Share source positivity/domination and optional upper packing bound with exact degree gaps, leading coefficients and concrete sharp exponents. | P-f:report/sections/03_architecture.tex:172-213. |
| EX033 | **Finite row envelope proof schema.** Replace NativeCoefficientBounds 22 row proofs with shared positivity/sign basis, abs_ite_le traversal and restricted linarith; preserve sharp transport dependence. | P-d:3; P-c:6. |
| EX034 | **Finite coefficient catalog or majorant.** Encode 25 values or sparse coefficient vectors over nonnegative monomial basis; checked table/evaluation equality derives original sharp envelope. | P-d:3.3; P-c:6.2. |
| EX035 | **Coefficient homomorphism compression.** Focused simp/generated finite-case tactic or single computable ring AST for Native/Gap mapRowCoefficient families; preserve authoritative table, CommRing and support. | P-f:report/sections/03_architecture.tex:214-253; P-c:6.1. |
| EX036 | **Sparse row equality checker.** Small normalized sparse quadratic syntax for Split/Gap/Native source-row identities, linked to independent recipe; not full finalizer expansion. | P-c:12.3. |
| EX037 | **Elementary row operations.** One addAt zero-set equivalence and surjective reindexing theorem for SplitCertificate59 transformed_zero_iff; preserve distinct source/destination. | P-c:13. |
| EX038 | **Existing run_power certificate.** Emit one actual-node exponent label table and PowerStep certificate, specialize run_power, retain all 193 named powers; shard if needed. | P-e:11; P-f:report/sections/04_circuits.tex:50-127; P-b:7.2; P-d:7.2; P-a:5.1. |
| EX039 | **Indexed node equation facade.** Shared per-circuit natural_step/run_node_equation helper or demand-driven generated specialization for 999 node facts; keep valuable cuts/public aliases. | P-e:11; P-f:report/sections/04_circuits.tex:128-166; P-b:7.3; P-d:7.1; P-a:5.2. |
| EX040 | **Generator respects semantic cuts.** Split sourceSRegister/sourceRankRegister use already proved high/S/T/block identities; snapshot cuts dictionary in generator to avoid later/self references. | P-c:7. |
| EX041 | **Shared topological invariant.** One indexed run_invariant strong induction for uniqueness, degree and nonnegativity, instantiating existing node equations/topology. | P-c:11; P-a:6. |
| EX042 | **Commutative node relation and translation.** Extend NodeRel with swapped add/mul, keep subtraction ordered; generic Split/Gap positive-natural simulation with prefix/reference/exception facts. | P-c:12.1; P-a:7.1. |
| EX043 | **Local append invariants.** Share NaturalRegisterProgram.push topology/allowed old-vs-last index splits and eval_old/eval_last append bookkeeping. | P-a:7.3. |
| EX044 | **Semantic block certificates.** Local symbolic value tables/recipe tail proofs linked to full existing DAG and output; retain independent high-level recipe and cutpoints. | P-e:11; P-f:report/sections/04_circuits.tex:167-187. |
| EX045 | **Shared ShortSystem degree prefix.** Factor exact 224-line common prefix of literal/compact degree proofs or existing degree checker with two tails, retaining <=68 and value bridges. | P-f:report/sections/04_circuits.tex:188-210. |
| EX046 | **Checked or dependent circuit views.** Bundle list/topology/bounded output or SafeNode operands Fin earlier with exact erasure equality; not new arithmetic circuit. | P-f:report/sections/04_circuits.tex:211-233. |
| EX047 | **Half-radix identity.** Derive (sa)%(2s)+(sb)/(2s)=s*(a%2)+b/2 for s>0; bound/parity replace NativeCyclicRotation enumeration. | P-b:8.1; P-d:4.1; P-c:5; P-a:9.2. |
| EX048 | **Shared full-modulus residues.** Low-level cyclic addition/subtraction and aligned arbitrary-shift normal forms, support-zero and off-origin mask lookup across current/legacy modules. | P-e:12; P-f:report/sections/02_local.tex:176-209; P-b:8.2; P-d:4.2; P-a:source_notes/digits-review.md:5. |
| EX049 | **Weaken reflected residue modulus.** CurrentEarlyPadding reflected_mod_sixteen from CurrentClause reflected_weight_mod modulo2048 via ModEq.of_dvd; identical selector definitions. | P-b:8.2; P-c:15; P-a:9.1. |
| EX050 | **Decode source-register equations once.** Shared q=1+Jβ,L=q²−1,N=q³,X=qw from literal rows for NativePellBootstrap/Power; separate positivity/rank/port bounds. | P-b:8.3. |
| EX051 | **Natural integer rank bridge.** Shared nativeRank.toNat cast equality/nonnegativity/lower bounds from actual positive source in NativePellFirstIndex and source-window proofs. | P-c:notes/arithmetic.txt:6. |
| EX052 | **Scalar decomposition API.** From raw=d+Bq derive quotient under d<B, residue when m divides B, and zero carry under raw<B; no unwarranted digit premise on residue/reset. | P-e:12; P-a:9.4. |
| EX053 | **Derived recurrence and small facts record.** CarryCertificate/WordFacts or smaller view of existing Facts; recurrence derives from digit bound+decomposition; source/word/mask layers distinct. | P-e:12; P-b:9.1; P-d:9.1; P-c:15; P-a:9.4. |
| EX054 | **Conditional padding witness.** Move existence of padding u inside middle-phase implication to remove dummy zero witness in CurrentCount2011 caller. | P-a:9.3. |
| EX055 | **Finite fiber pushforward.** One sum_fiber_mul identity for mass_foldStencil, convolution_foldStencil and word_foldStencil; allow collisions, retain modular power reasoning. | P-d:6. |
| EX056 | **Origin decrement word.** word_sub_origin with delta<=a 0 for CurrentHighDigits/NativeHighPort54 high_mask_word; preserve no-borrow hypothesis. | P-a:source_notes/digits-review.md:6. |
| EX057 | **Direct physical selector sum.** Expose selectorCount equality to physical Fin942 sum before prefix conversion; CurrentOneHot/FieldOffsets use direct equality. | P-a:source_notes/digits-review.md:7. |
| EX058 | **Chunk dispatch and sum assembly.** WangTiles942Data adjacent-block/balanced or Euclidean dispatcher, final partial block; CurrentKernel finite-sum tree; retain checked leaves. | P-e:13; P-b:9.2. |
| EX059 | **Copied-field direction descriptor.** One copiedFields_bounded or finite west/north/east/south descriptor for four control field offset/width/packed shifts; preserve tuple-order difference and collisions. | P-e:13; P-b:9.3. |
| EX060 | **Optional mask block library.** Reuse lookup/length/bound facts for second mask client; preserve low +1, high origin -1 and scalar beta shift distinctly. | P-e:13. |
| EX061 | **Shared direct/native graph builder.** Parameterize rawStepProgram/boundedRunProgram over small combinator record, retain native/direct realizers and exact costs 1742/6924. | P-e:14. |
| EX062 | **All-model sealed completeness bridge.** Centralize axioms_of_zfc_model extraction, semantic validity and seal_valid before completeness; retain universes, arbitrary/nonstandard models and contexts. | P-b:10.1; P-c:14; P-a:10.2. |
| EX063 | **Arity-polymorphic closed transport.** Generalize ObjectQuarticCompiler local closed helper to any Fin n, reuse at target arity or expose sat_noZeroForm_at_iff. | P-b:10.2; P-c:14.1. |
| EX064 | **Definable induction transport.** omega_ind_of_spec takes actual formula/environment/Sat equivalence; shares semantic transport, not unrestricted external predicate induction. | P-a:10.1. |
| EX065 | **Existing internal semiring interfaces.** Share only model-independent index/renaming or row-conjunction facts between ObjectQuadraticSystem/QuadraticRegisterComposition; preserve unguarded evalRel_unique. | P-d:8.4; P-c:14.2. |
| EX066 | **Specialize half_base_bound_31.** SelectiveCoefficientBounds specialization m=31 directly via half_base_bound and existing equality hypothesis. | P-f:report/sections/02_local.tex:10-54. |
| EX067 | **Use Finset intersection.** LowMaskCoding.sum_range_support and MultiTargetCarry.selectedMask_eq via filter_mem_eq_inter/inter_eq_right rather than ext membership proof. | P-f:report/sections/02_local.tex:105-144. |
| EX068 | **Predecessor exponent cancellation.** Seven hpow bodies use pow_succ' and Nat.sub_add_cancel ht instead of congr+omega; avoid double-counting deleted half_base specialization. | P-f:report/sections/02_local.tex:145-175. |
| EX069 | **Convolution distributivity tail.** NativeCyclicConvolution.word_convolution final factorization via sum_mul/mul_sum/pow_add and controlled AC simplification. | P-f:report/sections/02_local.tex:216-222. |
| EX070 | **Exact two-power lower bound.** NativeRadixDigits hr via Nat.one_lt_two_pow instead of weaker bound+normalization+omega. | P-f:report/sections/02_local.tex:223-228. |
| EX071 | **FiniteSwitch boundary normalization.** ArithmeticFiniteSwitch non-equality branch tag<count+1 iff tag<count eliminates redundant case split. | P-f:report/sections/02_local.tex:229-233. |
| EX072 | **cellDigit_lt branch expansion.** Optional split_ifs/norm_num replacing existing highDigits_lt specialization; report recommends retaining original unless measured benefit. | P-f:report/sections/02_local.tex:234-239. |
| EX073 | **Decoder-bound controller certificates.** Optional local controller invariant certificates bound to actual decoder; distinguish preservation from reachable initial states and all-cycle exclusion requiring ranking/SCC reasoning. | P-e:13. |
| EX074 | **Shared generator templates.** Consolidate Split/Gap generator proof templates while preserving public theorem names and intermediate cuts; generator maintenance rather than semantic circuit change. | P-e:11. |
| EX075 | **Narrow modules and explicit audits.** Thematic/light imports, preserve facade names, explicit affected Checks/Audit/checks targets beyond main umbrella; not new proof claim. | P-e:14-16. |

## Incoming extensions and notes-only exclusions

| ID | Existing mechanism and scope | Source evidence |
| --- | --- | --- |
| L01 | **Exact recursive decoder graph.** Fuse quote recovery and depth into one induction; use Option.bind_eq_some_iff to skip impossible failure branches; derive exact arbitrary-code/fuel iff and monotonicity. Separate successful-branch cleanup is also prior. | I-eight: Describe the tree decoder by its exact graph; I-directions: Fuse syntax-decoder correctness; I-review: decoder section; I-round2: 04_decoder.tex |
| L02 | **Total decoding for parent checker.** Use decodeTable_total and tableCode_of_decode to rewrite any raw parent list to a typed list, then apply check_lists. No re-encoding induction. | I-round2: 03_parents.tex |
| L03 | **Exact rational witness descent.** Take the existing rational root to its integer numerator by denominator-one power lemma; preserve sign and all joint equations; share general separated norm reconstruction below both finalizers. | I-eight: Preserve rational roots; I-additional: Preserve the exact rational root |
| L04 | **Whole-product unit decomposition.** Use IsUnit.mul_iff and Int.isUnit_iff once for all factors, resolving conditional sign exclusions without manufacturing complementary products. | I-eight: Decompose the product's units once |
| L05 | **Finite invariant predecessor/reflection.** Restrict an injective finite map to a forward-invariant predicate and obtain a predecessor by surjectivity. Offset-19 exclusion avoids full orbit arithmetic. | I-eight: Use finiteness to recover an invariant predecessor; I-six: Idea 6 |
| L06 | **Degree before support.** Bound natDegree of factors and product, then infer coefficient vanishing. Avoid expanded nested coefficient sums in SelectiveCarry. | I-eight: Prove the support envelope before individual coefficients |
| L07 | **Point-mass rotation.** Specialize existing word_convolution at Pi.single t 1; derive rotation congruence without another reindexed exponent sum. | I-eight: Rotation is convolution with a point mass |
| L08 | **Primrec compositional automation.** Register extensional Primrec and closure rules for fun_prop; synthesize formula-constructor proofs without changing explicit PR programs or costs. | I-eight: Automate extensional primitive-recursiveness composition |
| L09 | **Canonical digit/carry normalization.** Maximum principle proves carry uniqueness with raw vector and digits fixed; fixed-length ofDigits injectivity derives digits from equal full words; canonical window normalization follows only after strict representative is fixed. | I-eight: Canonical normalization from a finite maximum principle |
| L10 | **Signed modular relation.** Compose congruence up to sign using symmetry/transitivity/multiplication/powers and natAbs bridges; guarded half-interval uniqueness is also in notes. | I-directions: Treat Pell sign ambiguity; I-ideas: Make congruence up to sign compositional; I-additional: Compose congruence up to sign |
| L11 | **Internal tagged views and unique existence.** One constructor-view theorem replaces BoundStep disjunction inversions, and one definable internal ∃! induction replaces separate totality/uniqueness. Preserve nonstandard codes. | I-directions: Constructor views and one internal unique-existence induction |
| L12 | **Internal recursive-graph laws.** Prove ThetaG preservation and fusion using totality, functionality and explicit definability of stage invariants; addition, multiplication and closure are clients. | I-directions: Preservation and fusion for internal recursive graphs |
| L13 | **Depth-budget interpreter.** Baseline/excess max-plus certificates recover GraphRep depth bounds, with local adapters, AST traversal, let-sharing and memoization; factorial/product plans supplied. | I-directions: Synthesize representation-depth bounds with small certificates |
| L14 | **Closed cyclic carry formulas.** Rotated weighted sums give least/greatest carries, exact one/two-solution classification and budget-selected least witness. Explicit construction and uniqueness are prior. | I-directions: An optional structural alternative: explicit cyclic carries |
| L15 | **Zero-or-singleton finite support.** Use Finset.sum_le_one_iff for all-zero or one selected index; preserve the empty type case. | I-ideas: Use the existing finite-support classification; I-round2: 05_finite_and_cycle.tex; I-simplification: Use the existing sum-at-most-one API |
| L16 | **Pell parity reuse.** Invoke SignedPellResidue.odd_index_of_base_dvd in NativePellStepDown and delete unused local positive-index proof. | I-ideas: Reuse the already proved Pell parity criterion; I-six: Idea 2; I-additional: Reuse the existing odd-index theorem |
| L17 | **Pairing inverse-graph projections.** Eliminate a coordinate of forward graph via product equivalence; normalize Fin witnesses then consume existing certificate iff. Includes quadratic pairing/tree graphs and prospective Cantor application. | I-ideas: Derive inverse graphs from a product equivalence; I-additional: pairing graph section |
| L18 | **Euclidean certificate uniqueness.** Share positive-denominator quotient/remainder/slack certificate and identify all its witnesses; extend coherence to composed witnesses. | I-ideas: Share the positive-denominator Euclidean certificate and further questions |
| L19 | **Affine composition budget.** One witness/depth potential pays composition overhead, including coefficient-six Thin invariant, aggregate child witnesses, and direct-versus-indirect zero-arity distinction. | I-ideas: Factor the arithmetic budget behind composition |
| L20 | **Support-restricted evaluator/frame rules.** Propose support-only evaluator congruence and overwrite/frame lemmas; notes acknowledge existing WitnessCompaction.eval_congr. Notes-only still excluded. | I-directions: evidence/prior_ideas.md candidate 7 |
| L21 | **Schema index-map normalization.** Normalize rsep/rf1/rf2/ri renaming chains through algebra of index maps in AnnotatedSchemaMaps. Notes-only still excluded. | I-directions: evidence/semantic_review.md section 5 and evidence/prior_ideas.md candidate 8 |
| L22 | **Cyclic packing by universal property.** Represent word packing as monoid-algebra hom into ZMod(radix^n-1); deduce convolution/product and rotation/monomial laws. Notes-only still excluded. | I-directions: evidence/algebra_review.md final optional direction and evidence/prior_ideas.md candidate 9 |
| L23 | **Delete unused internal inductions.** Use nat_zero_or_succ for ObjectAdditionCancellation.addRel_zero_iff and ObjectNaturalZero.mulRel_zero_iff when successor branches never use induction hypotheses; remove private stage formulas. | I-six: Idea 1; I-roadmap: Delete internal inductions whose hypotheses are unused |
| L24 | **Abstract signed divisibility witnesses.** Use closure of divisibility under subtraction/negation and existing ModEq conclusions instead of extracting and reconstructing witnesses for signed endpoints. | I-six: Idea 3 |
| L25 | **Pell base monotonicity.** Compare bases via positive pair recurrence and simultaneous x/y monotonicity, removing exponential detours in main_index_gt_first. Actual value gap is enough for index comparison. | I-six: Idea 4; I-residual: Compare Pell bases through the positive pair recurrence |
| L26 | **Integer-domain norm proof.** Prove norm_ne_zero_of_not_isSquare wholly over integers using square/divisibility facts; avoid rational squarehood detour. | I-six: Idea 5 |
| L27 | **Negative Pell from positive units.** Square a hypothetical negative-norm solution, classify positive unit powers, and use their first-coordinate congruence to contradict norm -1. | I-roadmap: Derive the negative Pell obstruction from positive units |
| L28 | **Normalize residue obstructions.** Reduce multiple three-residue norm obstructions to the existing shifted ShortEquation.strong_ne_neg_one theorem; one shared discriminant normal form. | I-roadmap: Normalize three residue obstructions to one existing theorem |
| L29 | **Minimum saturation.** Use equality of a sum with the sum of heterogeneous lower bounds to obtain every block equality, including coupled nonzero minima in MinimumNorm.minima76_zero_iff. | I-roadmap: Extract all block equalities from one minimum-saturation theorem |
| L30 | **Monotone local-certificate closure.** One calculus for empty/union/insert certificates over arbitrary internal set carriers, deriving repeated BoundClosed constructors and naturalness. | I-roadmap: Optional: a calculus for monotone local certificates |
| L31 | **Scale-parametric Pell ratio estimate.** General real error factor covers upper_estimate and upper_estimate_scaled through the same proof; old interfaces become specializations. | I-five: A: one Pell estimate with an explicit error factor |
| L32 | **Natural perturbation and power sandwich.** Replace analytic perturbed powers with natural-number inequality and transfer through Pell growth bounds; expose separate error budget instead of stronger global threshold. | I-residual: A natural-number perturbation kernel for both Pell upper bounds |
| L33 | **Exact half-binomial quotient.** Identify lower binomial block as remainder, then recover half-binomial value via exact integer half-quotient rounding under one error inequality. | I-residual: Recover the half-binomial value through an exact integer quotient |
| L34 | **Arbitrary-premise fragments.** Collect any list of proof fragments with suffix-history-length parent indices and finish the rule once; preserve reversed history convention and derive old arity wrappers. | I-five: B: construct proof fragments for any number of premises |
| L35 | **Successor-indexed fork certificate.** State ForkCertificate(out+1) equivalence first, then isolate impossible zero once; avoid natural predecessor cancellation in each branch. | I-five: C: prove fork certificates at successors first |
| L36 | **Projected support-difference separation.** Under additive projection, displacement outside S-S forces one supported factor to vanish; used with actual native support and existing no_difference_606. | I-five: D: separate supports through a quotient homomorphism |
| L37 | **Canonical square-pairing auxiliary witnesses.** Characterize selector, slack and max witnesses as well as output pair code; full row equivalence gives deterministic existing witnesses. | I-five: E: pairing certificates have canonical witnesses |
| L38 | **Shared executable and semantic rule schedules.** Define ordered tag/rule schedule syntax once, interpret as Boolean validity and PR computation, and certify erasure to existing frozen programs. | I-residual: Define rule schedules once and derive both interpretations |
| L39 | **Direct South prefix use.** Apply binaryWord_prefix at (1,8) and (2,7) then normalize addresses inside lambdas; eliminate redundant function equalities for offsets19/20. | I-round2: 06_south_prefix.tex; I-deltas: pageheading 4 |
| L40 | **Hoist binary word congruence.** Move existing binaryWord_congr to definition layer; horizontal_words and copy_word_translation no longer reopen finite sums. | I-round2: 07_word_congruence.tex |
| L41 | **Cycle reachability reuse.** Use theta a.val b as exact difference-cell witness, and derive zero-base propagate from propagate_from; no new coordinate abstraction. | I-deltas: pageheading 5; I-round2: 05_finite_and_cycle.tex |
| L42 | **Boundary high-color fibers.** Guarded equality-indexed North/South fibers, or NorthView by color, replace repeated eliminations in eight boundary classifiers while keeping literal initializer/seam tuples. | I-deltas: pageheadings 6–7; I-round2: 08_north_view.tex |
| L43 | **Selector assignment coherence.** Characterize alternate assignment from selected bits in the same original word and inverse coordinate; transport facts_marked_word by resulting equality. | I-deltas: pageheading 8 |
| L44 | **Explicit CRT congruence transport.** Replace gcongr/exact? in BoundedForallCertificate with add_right/mul_right/add_right applied to the existing congruence witness. | I-round2: 09_supplemental.tex S1 |
| L45 | **Binary composition depth helper.** Factor Fin2 elimination in five BoundedForallDepth wrappers, preserving h+8 bounds; charge support overhead. | I-round2: 09_supplemental.tex S2 |
| L46 | **Small-ordinate Pell fundamental criterion.** Use classification of fundamental-unit powers to prove any positive solution with y≤3 is fundamental; criterion sharp at y=4. | I-additional: A uniform small-ordinate criterion for Pell minimality |
| L47 | **Quadratic Boolean existential certificate.** Consume exists_zero_certificate_iff before conditional branching; eliminate slack via existential/conjunction rearrangement, preserving whole Rep data. | I-additional: Consume the Boolean certificate before constructing a conditional |
| L48 | **Physical-position injectivity by positive tail.** Recognize physicalPosition as Fin.cons zero positive strictRank-tail, invoke Fin.cons_injective_iff and compose existing injections. | I-additional: Optional: recognize the physical permutation as a positive tail |
| L49 | **Finite-word representation boundary.** Unify ZMod/Fin/List.ofFn and finite-sum conversion; geometry wrapper for range and wrap facts; distinct from proving a new packing theorem. | I-review: Unify modular and finite-word interfaces |
| L50 | **Decoder codec left inverse.** Shared parse-then-check and decoder left-inverse→quote injectivity; successful Option bind destructuring is explicit in earlier reports. | I-simplification: Reuse parser and list infrastructure; I-review: Shorten decoder proofs |
| L51 | **Full invertible row transformations.** General invertible linear row combinations are already mentioned as a later extension to elementary row-addition zero-set invariance. | P-c: Represent elementary row operations once |
| L52 | **Sum-index witness regrouping.** Use Sum.exists_sum plus one cast identity for Sum.rec to regroup DAG input/witness valuations; preserve topology/output/Allowed guards. | I-review: evidence/structural/findings.txt section 3 |
| L53 | **Dedicated natural evaluator option.** A natural-semiring evaluator with erasure-correctness to ArithmeticDAG is already proposed as an optional alternative to repeated casts/positivity. | I-review: evidence/structural/findings.txt section 7 |
| L54 | **Guarded binary/unary constructor witnesses.** Move binaryForm/unaryForm early and share code_binaryForm, renamed_binaryForm and bound_binaryForm, avoiding repeated three-tag witnesses in Rename/Bound soundness. | I-review: evidence/syntax/findings.txt section 6 |
| L55 | **Pair-zero and degree-renaming consolidation.** Publish zero_pair once for three annotated modules and reuse expression syntaxDegree_rename; these local algebra cleanups are notes-only but explicit. | I-review: evidence/syntax/findings.txt section 7 |
| L56 | **Replace artificial existential lets.** Use set ... with equality in NativeHalfBinomial.upper_estimate_scaled instead of obtaining trivial existential witnesses. This readability change is already proposed. | I-review: evidence/arithmetic/findings.txt section 8 |

## Broad prior directions that are not blank territory

- Functional-graph uniqueness, split-encoding projections, relation algebra for solvability, natural-difference/order-embedding bounds and syntax-recursive pair induction appear in exploratory notes. A new concrete theorem may differ, but should cite this nearest direction.
- Generic finite controller certificates, rankings and SCC-based all-cycle exclusion are already mentioned. An actual new Lyapunov invariant could be new work; proposing to create such certificates in general is not.
- Profiling, restricted simp sets, axiom audits, import cuts, generator synchronization, sharded certificates and measuring helpers as well as clients are established methodology in the corpus, not new recommendations.
- The current total_degree_bound tactic is also already upstream; re-proposing it cannot count as novel.

## Candidate screening performed in this review

| Candidate | Closest prior mechanism | Screen result |
| --- | --- | --- |
| Helical row normalization by a period `(w,-1)` on `ℤ×ℤ`, then integer multiples | EX048 full-modulus geometry; L41 cycle propagation | No prior matching proposal found. Distinct obligation: bilateral external integer induction is replaced by translation-period closure. Generic quotient geometry is not claimed new. |
| Exact selector mass through four affine color moments | EX058 checked chunk/sum assembly; EX059 packed fields | No prior matching proposal found. Distinct certificate quantity and affine decomposition; charge all family-moment proofs. |
| `large_of_six_le` from a fixed index-six lower bound via `xn_ge_a_pow` at five and index monotonicity | L25 base monotonicity; L46 fundamental small-ordinate criterion | No prior matching proposal found. Three prior patched Bootstrap files retain the old variable-exponent proof unchanged. Do not claim generic monotonicity is new. |
| Direction-indexed local signal/receive semantics | EX059 arithmetic direction descriptor; L42 boundary fibers | No prior matching proposal found. Requires a shared semantic argument despite asymmetric signal rails; factoring names alone is insufficient. |
| Canonical `stepTile` row reconstruction, then south-row theorem as projection | L43 selected assignment coherence; L11 internal unique existence | No prior matching proposal found. Distinct proposed invariant is uniqueness of whole local machine-row realization. Must prove it without circularly using the theorem it replaces. |
| Shared edge-field row construction, with west(x)=E(x−1) and east(x)=E(x) | EX059 packed-field arithmetic; L42 boundary views | WITHDRAWN after freshness refresh: packet U and Round3 already propose the shared edge, pulse, literal stepTile bridge and unconditional-state adapter. See F11. |
| Centered `Int.inductionOn'` for bounded `interval_propagate` | EX007 Nat scanner induction; L41 finite-cycle propagation | WITHDRAWN after freshness refresh: packet U explicitly supplies centered Int.inductionOn' and Round3 supplies translated integer induction for this same theorem. See F10. |
| Direct twisted finite band to marked word | EX048 Cell/ZMod coordinate interface | No explicit prior match, but not recommended without concrete deleted proof cost. Existing infinite-plane pipeline is already short; novelty alone does not make it useful. |

Screen results are limited to overlap. They do not certify mathematical validity, Lean compilation, integrated source reduction or performance. Actual verification belongs in the new report’s separate evidence record.

## Reproducibility artifacts

- `incoming-manifest.json`: every archive member, size and SHA-256; extracted text paths retained for local replay.
- `placed-manifest.json`: every file in the six placed packets, size and SHA-256.
- `report-key.json`, `report-section-index.json`: exact main-manuscript locators and section lines.
- `exclusions.json`: machine-readable coverage entries.
