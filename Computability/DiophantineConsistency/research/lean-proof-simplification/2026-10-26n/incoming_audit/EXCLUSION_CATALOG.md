# Prior proof simplification ideas

Review pinned to ProveIt `b310142330df89e48413c8fce62e7de223e1c7d5`.

The catalog records 75 prior proposal families from all five ZIPs currently in `docs/incoming`, plus the retired sixth packet explicitly linked by its README. All six archive byte streams were checked against their Git blob SHA-1 and recorded with SHA-256. All six manuscripts and their technical proposal notes were inspected; candidate names and relevant source artifacts were cross-checked. No submitted executable or Lean compiler was run.

## How novelty is decided

An idea is excluded when it repeats the same mathematical or proof-engineering mechanism at the same target or announced consumer family, even if renamed or written with different tactics. A generic mention of library reuse, induction, finite certificates or records does not exclude every future use of that technique. A distinct local theorem, eliminated proof obligation or new semantic classification can remain novel; its connection to prior work should be stated. Merely claiming a new application of an already proposed shared API is not a new proposal. Baseline source copies inside an archive are evidence of the old code, not proposals to change it.

Reported compile receipts in prior packets are their historical claims, not new validation by this audit. The exclusion decision does not depend on whether the old proposal was compiled, adopted or still only sketched.

## Source key

- **A** [Lean_Proof_Simplification_2026-10-26.zip](https://github.com/VladimirReshetnikov/ProveIt/blob/b310142330df89e48413c8fce62e7de223e1c7d5/docs/incoming/Lean_Proof_Simplification_2026-10-26.zip), manuscript `Lean_Proof_Simplification/report/report.tex`. Git blob `28e8215b4b8d80d5187c5b1aeaacfa9cacadb6f3`; SHA-256 `dda8929e3e159c3f165b469dbdaacd9e180e30e4a90fb62abe3ecff69a6d58ac`.
- **B** [ProveIt_Lean_Proof_Simplification_2026-10-26.zip](https://github.com/VladimirReshetnikov/ProveIt/blob/b310142330df89e48413c8fce62e7de223e1c7d5/docs/incoming/ProveIt_Lean_Proof_Simplification_2026-10-26.zip), manuscript `LeanReview/report/proof_simplification_report.tex`. Git blob `55730040e6410fb7f530d84018e4cd6ecb80e961`; SHA-256 `2a0f51271b3d327a2916f66273b999f09e8c2fbebd69489102e2558e397d3f1e`.
- **C** [diophantine-lean-simplification-2026-10-26.zip](https://github.com/VladimirReshetnikov/ProveIt/blob/b310142330df89e48413c8fce62e7de223e1c7d5/docs/incoming/diophantine-lean-simplification-2026-10-26.zip), manuscript `diophantine-lean-simplification-2026-10-26/report.tex`. Git blob `065a4cbf9fde2ef0b15db9898920e84d7a3b49fb`; SHA-256 `f05ee2789f3cfbca29467377aeaaef6972211406807ce45d4590459621c86470`.
- **D** [lean-proof-simplification-2026-10-26 (2).zip](https://github.com/VladimirReshetnikov/ProveIt/blob/b310142330df89e48413c8fce62e7de223e1c7d5/docs/incoming/lean-proof-simplification-2026-10-26%20(2).zip), manuscript `lean-proof-simplification-2026-10-26/report.tex`. Git blob `1ff01cc5a18b9f3043b6778f3e45da66bf90f4bb`; SHA-256 `5035e9a719f7504dfc5c035b2675bbcdf207e9b81c5cbcc28f6112d9be1cdc56`.
- **E** [lean-proof-simplification-2026-10-26.zip](https://github.com/VladimirReshetnikov/ProveIt/blob/b310142330df89e48413c8fce62e7de223e1c7d5/docs/incoming/lean-proof-simplification-2026-10-26.zip), manuscript `lean-proof-simplification-2026-10-26/report.tex`. Git blob `2f7a1482e17ae06fb45fb9a92a655d30096e50cb`; SHA-256 `a7d630331b4f50b653a57de9c3b8f1958762d4b2257e65da1e1de17302182c20`.
- **F** [diophantine-lean-proof-simplification-2026-10-26.zip](https://github.com/VladimirReshetnikov/ProveIt/blob/151a732b910342930f57a775baa1e5ed1abe09d7/docs/incoming/diophantine-lean-proof-simplification-2026-10-26.zip), manuscript `lean-proof-simplification/report.tex`. Git blob `9f015d03d918b79f8a5b9baa101420297de46cab`; SHA-256 `f03f894362c9811fcda4c34d35e3a2a657c8f6a51278ee84cbdd98724304bde1`.
  Retired after arrival `151a732b910342930f57a775baa1e5ed1abe09d7`; [placed manuscript at review pin](https://github.com/VladimirReshetnikov/ProveIt/blob/b310142330df89e48413c8fce62e7de223e1c7d5/Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/report.tex).

## Catalog

Locators give packet ID and report section; explicit member paths and line ranges override section numbering. For F digit notes, trailing numbers mean the numbered note heading, not line numbers.

### EX001 Seven private optional-list-lookup inductions
**Library reuse.** Use List.mem_of_getElem? and List.getElem?_of_mem or mem_iff_getElem? at AnnotatedRename, Bound, ProofChecker, Assumption, RuleSide; wrappers or direct replacement.
Sources: A:6; C:3; D:9.2; E:3; F:3.2.

### EX002 Option map injectivity
**Library reuse.** Replace AnnotatedParents judgment-code option case split by Option.map_injective judgmentCode_injective.
Sources: A:6.

### EX003 Realizer and optimizer recursor congruence
**Primitive recursion.** Eliminate inner Nat.rec induction in PRCode.Realizes.prec, ScalarPRCode.Realizes.prec and ScalarPROptimizer.eval_optimize by explicit simp or shared axiom-free RecursorCore.rec_congr.
Sources: F:3.1.

### EX004 Assignment naturality
**Representation.** Shared natAssignment composed with Sum.map and Expr.eval_rename for reindex/conjunction/disjunction/existsBlock; preserve expression fields and counts.
Sources: C:4.1-4.2; D:2; E:4; F:3.3.

### EX005 Concatenated witness existential
**Representation.** Generic equivalence between Fin(m+n) witness and two Fin blocks via Fin.addCases, including zero lengths.
Sources: C:4.1.

### EX006 Early witness-count projections
**Representation.** Move existing constructor count projection lemmas from RepresentationSize to constructors or lightweight module to avoid unfolding large data.
Sources: C:4.3.

### EX007 Recursor iteration mechanics
**Scanner.** Share fixed points, zero/done stability, successor-right/left and invariant or reject-or-good laws across five scanners and ContextLookup; keep executable Nat.rec definitions.
Sources: A:7; C:5.2; D:5; E:9; F:8.1.

### EX008 Encoded-step semiconjugacy
**Scanner.** Share typed/encoded iterator fusion and scan-list/table simulation from exact step_cons/terminal/reject laws; includes AnnotatedClosure coding/execution induction.
Sources: A:7; C:5.2; E:9; F:8.1.

### EX009 Guarded-history fold
**Scanner.** Share run_append, run_sound, Produces.append and Produces.step for Rename/Bound/ProofChecker with distinct Line/Judgment types and emit function.
Sources: A:8; C:5.1; E:9.2.

### EX010 Explicit dynamic-seed PR iterator
**Scanner.** Introduce iterateFrom with realized seed/fuel and parameterized step for scanner PR builders; preserve .val program and single expensive validator.
Sources: C:5.3; E:9.3.

### EX011 Exact numeric Boolean reflection
**Scanner.** Derive check=truth valid from 0-or-1 range and check=1 iff valid=true, then simplify Bound/Rename step_cons.
Sources: A:8; C:5.4; F:8.2.

### EX012 Common tag threshold dispatcher
**Scanner.** One arithmetic theorem for 0/1,2,3/4/5,6/7 and >=8 outcomes in BoundLocal/RenameLocal, over all natural tags.
Sources: A:8; C:5.4.

### EX013 Carrier finite positivity enumeration
**Algebra.** After fin_cases infer coordinate via hv _ in Carrier66.drop_pos/restore_pos instead of enumerating exact indices.
Sources: A:3.

### EX014 Carrier canonical zero normalization
**Algebra.** Replace canonical_zero unfold/rw/ring by narrow simp using canonical equalities.
Sources: A:3.

### EX015 Integer units
**Algebra.** Use Int.eq_one_or_neg_one_of_mul_eq_one in ShortSystem.unit_eq_one and reuse uniformly in product_eq_one_iff with sign exclusions.
Sources: A:4.

### EX016 Five residual squares
**Algebra.** ShortSystem.residualSum_zero_iff via nonnegative-add/square-zero lemmas or Finset.sum_mul_self_eq_zero_iff rather than repeated nlinarith.
Sources: A:4; B:report/sections/02_local.tex:55-104; F:4.1.

### EX017 Common executable residual aggregation
**Compiler.** Share eval_sumExpressions/sumSquares zero iff, degree <=2d and parameterized (b+1)*length cost bound across DAGQuartic, NaturalDAGQuartic, QuadraticRegisterSystem, QuarticCost.
Sources: C:6.1; D:8.1; E:10; F:4.2.

### EX018 Shared semiring gate induction
**Compiler.** Extract GatesSyntax/data below generic semiring soundness/completeness then derive natural/integer compiler theorems without import cycle.
Sources: C:6.2; D:8.3.

### EX019 Merge identical constructor branches
**Compiler.** QuarticCompiler.Gates.complete add/mul proof alternatives share one branch.
Sources: A:5.

### EX020 Move syntax degree and rename laws earlier
**Compiler.** Canonical Expr polynomial_rename, syntaxDegree/polynomial_degree_le at expression layer; weighted degree at constant weight one; keep cancellation-aware normal forms.
Sources: C:6.2; D:8.2; F:7.2.

### EX021 Generic RHS degree interface
**Compiler.** Share DAGQuartic/NaturalDAGQuartic node RHS degree <=2 from wire degree <=1 and small degree add/sub helpers.
Sources: A:11.

### EX022 Shorter run_map induction step
**DAG.** Use map_append/map_singleton/Node.eval_map directly at recursive boundary in ArithmeticDAG.run_map.
Sources: A:5.

### EX023 Cast Pell conclusion as a whole
**Algebra.** Replace FirstPellCarrier.first_norm_facts_int final disjunction split by exact_mod_cast hgap, retaining lifts and divisibility guards.
Sources: A:5.

### EX024 Shared DivMod certificate
**Arithmetic.** One neutral arithmetic certificate_iff for QuadraticDivMod/RegisterDivMod; retain separate realizers and witness counts 1/23.
Sources: A:6.

### EX025 Identical scalar tail
**Polynomial.** Extract SplitNinePolynomial59/GapNinePolynomial66 ratioValue with common map/cast laws and aliases; keep recipe exponents and b factor distinct.
Sources: A:9; E:8.

### EX026 Identical 99-node free-carrier tail
**Polynomial.** Common boundary-port block for Split 416..514 and Gap 385..483 under reference renaming; prove embedding and common ratioValue semantics, no copy gates.
Sources: E:8.

### EX027 Guarded solution transport
**Carrier.** HasSolution(D,P) congruence/composition via two existential directions, not assignment bijection; Current69/70/71 same-domain examples.
Sources: A:10.

### EX028 Nine-coordinate existence packaging
**Carrier.** Parameterize evaluator to share SplitSourceExistence/GapSourceExistence66 positive/natural coordinate existential proofs; slot7 unshifted internally.
Sources: B:report/sections/03_architecture.tex:11-67.

### EX029 Named conjunction accessors
**Carrier.** Derived Canonical.Z_eq_delta/index_eq_one/rank_pos and PortBounds/core positivity accessors without changing conjunction definition.
Sources: B:report/sections/03_architecture.tex:68-98.

### EX030 Coherent restored source and scalar window
**Window.** One actual source assignment and positive N yielding both low/high mask tests, shared Carrier65->66 restoration and radix power normalization.
Sources: B:report/sections/03_architecture.tex:99-146; F:source_notes/digits-review.md:8.

### EX031 Base interface below completeness
**Window.** CurrentCarrierBase2011 below ThirteenCarrierComplete, old facade retained, simpler digit clients redirected.
Sources: B:report/sections/03_architecture.tex:147-171.

### EX032 Parameterized Split/Gap degree profile
**Bounds.** Share source positivity/domination and optional upper packing bound with exact degree gaps, leading coefficients and concrete sharp exponents.
Sources: B:report/sections/03_architecture.tex:172-213.

### EX033 Finite row envelope proof schema
**Coefficients.** Replace NativeCoefficientBounds 22 row proofs with shared positivity/sign basis, abs_ite_le traversal and restricted linarith; preserve sharp transport dependence.
Sources: D:3; E:6.

### EX034 Finite coefficient catalog or majorant
**Coefficients.** Encode 25 values or sparse coefficient vectors over nonnegative monomial basis; checked table/evaluation equality derives original sharp envelope.
Sources: D:3.3; E:6.2.

### EX035 Coefficient homomorphism compression
**Coefficients.** Focused simp/generated finite-case tactic or single computable ring AST for Native/Gap mapRowCoefficient families; preserve authoritative table, CommRing and support.
Sources: B:report/sections/03_architecture.tex:214-253; E:6.1.

### EX036 Sparse row equality checker
**Coefficients.** Small normalized sparse quadratic syntax for Split/Gap/Native source-row identities, linked to independent recipe; not full finalizer expansion.
Sources: E:12.3.

### EX037 Elementary row operations
**Rows.** One addAt zero-set equivalence and surjective reindexing theorem for SplitCertificate59 transformed_zero_iff; preserve distinct source/destination.
Sources: E:13.

### EX038 Existing run_power certificate
**DAG.** Emit one actual-node exponent label table and PowerStep certificate, specialize run_power, retain all 193 named powers; shard if needed.
Sources: A:11; B:report/sections/04_circuits.tex:50-127; C:7.2; D:7.2; F:5.1.

### EX039 Indexed node equation facade
**DAG.** Shared per-circuit natural_step/run_node_equation helper or demand-driven generated specialization for 999 node facts; keep valuable cuts/public aliases.
Sources: A:11; B:report/sections/04_circuits.tex:128-166; C:7.3; D:7.1; F:5.2.

### EX040 Generator respects semantic cuts
**DAG.** Split sourceSRegister/sourceRankRegister use already proved high/S/T/block identities; snapshot cuts dictionary in generator to avoid later/self references.
Sources: E:7.

### EX041 Shared topological invariant
**DAG.** One indexed run_invariant strong induction for uniqueness, degree and nonnegativity, instantiating existing node equations/topology.
Sources: E:11; F:6.

### EX042 Commutative node relation and translation
**DAG.** Extend NodeRel with swapped add/mul, keep subtraction ordered; generic Split/Gap positive-natural simulation with prefix/reference/exception facts.
Sources: E:12.1; F:7.1.

### EX043 Local append invariants
**DAG.** Share NaturalRegisterProgram.push topology/allowed old-vs-last index splits and eval_old/eval_last append bookkeeping.
Sources: F:7.3.

### EX044 Semantic block certificates
**DAG.** Local symbolic value tables/recipe tail proofs linked to full existing DAG and output; retain independent high-level recipe and cutpoints.
Sources: A:11; B:report/sections/04_circuits.tex:167-187.

### EX045 Shared ShortSystem degree prefix
**DAG.** Factor exact 224-line common prefix of literal/compact degree proofs or existing degree checker with two tails, retaining <=68 and value bridges.
Sources: B:report/sections/04_circuits.tex:188-210.

### EX046 Checked or dependent circuit views
**DAG.** Bundle list/topology/bounded output or SafeNode operands Fin earlier with exact erasure equality; not new arithmetic circuit.
Sources: B:report/sections/04_circuits.tex:211-233.

### EX047 Half-radix identity
**Native arithmetic.** Derive (sa)%(2s)+(sb)/(2s)=s*(a%2)+b/2 for s>0; bound/parity replace NativeCyclicRotation enumeration.
Sources: C:8.1; D:4.1; E:5; F:9.2.

### EX048 Shared full-modulus residues
**Native geometry.** Low-level cyclic addition/subtraction and aligned arbitrary-shift normal forms, support-zero and off-origin mask lookup across current/legacy modules.
Sources: A:12; B:report/sections/02_local.tex:176-209; C:8.2; D:4.2; F:source_notes/digits-review.md:5.

### EX049 Weaken reflected residue modulus
**Native arithmetic.** CurrentEarlyPadding reflected_mod_sixteen from CurrentClause reflected_weight_mod modulo2048 via ModEq.of_dvd; identical selector definitions.
Sources: C:8.2; E:15; F:9.1.

### EX050 Decode source-register equations once
**Pell.** Shared q=1+Jβ,L=q²−1,N=q³,X=qw from literal rows for NativePellBootstrap/Power; separate positivity/rank/port bounds.
Sources: C:8.3.

### EX051 Natural integer rank bridge
**Pell.** Shared nativeRank.toNat cast equality/nonnegativity/lower bounds from actual positive source in NativePellFirstIndex and source-window proofs.
Sources: E:notes/arithmetic.txt:6.

### EX052 Scalar decomposition API
**Carry.** From raw=d+Bq derive quotient under d<B, residue when m divides B, and zero carry under raw<B; no unwarranted digit premise on residue/reset.
Sources: A:12; F:9.4.

### EX053 Derived recurrence and small facts record
**Carry.** CarryCertificate/WordFacts or smaller view of existing Facts; recurrence derives from digit bound+decomposition; source/word/mask layers distinct.
Sources: A:12; C:9.1; D:9.1; E:15; F:9.4.

### EX054 Conditional padding witness
**Carry.** Move existence of padding u inside middle-phase implication to remove dummy zero witness in CurrentCount2011 caller.
Sources: F:9.3.

### EX055 Finite fiber pushforward
**Native arithmetic.** One sum_fiber_mul identity for mass_foldStencil, convolution_foldStencil and word_foldStencil; allow collisions, retain modular power reasoning.
Sources: D:6.

### EX056 Origin decrement word
**Native arithmetic.** word_sub_origin with delta<=a 0 for CurrentHighDigits/NativeHighPort54 high_mask_word; preserve no-borrow hypothesis.
Sources: F:source_notes/digits-review.md:6.

### EX057 Direct physical selector sum
**Native arithmetic.** Expose selectorCount equality to physical Fin942 sum before prefix conversion; CurrentOneHot/FieldOffsets use direct equality.
Sources: F:source_notes/digits-review.md:7.

### EX058 Chunk dispatch and sum assembly
**Finite data.** WangTiles942Data adjacent-block/balanced or Euclidean dispatcher, final partial block; CurrentKernel finite-sum tree; retain checked leaves.
Sources: A:13; C:9.2.

### EX059 Copied-field direction descriptor
**Native layout.** One copiedFields_bounded or finite west/north/east/south descriptor for four control field offset/width/packed shifts; preserve tuple-order difference and collisions.
Sources: A:13; C:9.3.

### EX060 Optional mask block library
**Native masks.** Reuse lookup/length/bound facts for second mask client; preserve low +1, high origin -1 and scalar beta shift distinctly.
Sources: A:13.

### EX061 Shared direct/native graph builder
**Enumerators.** Parameterize rawStepProgram/boundedRunProgram over small combinator record, retain native/direct realizers and exact costs 1742/6924.
Sources: A:14.

### EX062 All-model sealed completeness bridge
**Object theory.** Centralize axioms_of_zfc_model extraction, semantic validity and seal_valid before completeness; retain universes, arbitrary/nonstandard models and contexts.
Sources: C:10.1; E:14; F:10.2.

### EX063 Arity-polymorphic closed transport
**Object theory.** Generalize ObjectQuarticCompiler local closed helper to any Fin n, reuse at target arity or expose sat_noZeroForm_at_iff.
Sources: C:10.2; E:14.1.

### EX064 Definable induction transport
**Object theory.** omega_ind_of_spec takes actual formula/environment/Sat equivalence; shares semantic transport, not unrestricted external predicate induction.
Sources: F:10.1.

### EX065 Existing internal semiring interfaces
**Object theory.** Share only model-independent index/renaming or row-conjunction facts between ObjectQuadraticSystem/QuadraticRegisterComposition; preserve unguarded evalRel_unique.
Sources: D:8.4; E:14.2.

### EX066 Specialize half_base_bound_31
**Local bounds.** SelectiveCoefficientBounds specialization m=31 directly via half_base_bound and existing equality hypothesis.
Sources: B:report/sections/02_local.tex:10-54.

### EX067 Use Finset intersection
**Local finite sums.** LowMaskCoding.sum_range_support and MultiTargetCarry.selectedMask_eq via filter_mem_eq_inter/inter_eq_right rather than ext membership proof.
Sources: B:report/sections/02_local.tex:105-144.

### EX068 Predecessor exponent cancellation
**Local powers.** Seven hpow bodies use pow_succ' and Nat.sub_add_cancel ht instead of congr+omega; avoid double-counting deleted half_base specialization.
Sources: B:report/sections/02_local.tex:145-175.

### EX069 Convolution distributivity tail
**Local arithmetic.** NativeCyclicConvolution.word_convolution final factorization via sum_mul/mul_sum/pow_add and controlled AC simplification.
Sources: B:report/sections/02_local.tex:216-222.

### EX070 Exact two-power lower bound
**Local arithmetic.** NativeRadixDigits hr via Nat.one_lt_two_pow instead of weaker bound+normalization+omega.
Sources: B:report/sections/02_local.tex:223-228.

### EX071 FiniteSwitch boundary normalization
**Local dispatch.** ArithmeticFiniteSwitch non-equality branch tag<count+1 iff tag<count eliminates redundant case split.
Sources: B:report/sections/02_local.tex:229-233.

### EX072 cellDigit_lt branch expansion
**Local masks.** Optional split_ifs/norm_num replacing existing highDigits_lt specialization; report recommends retaining original unless measured benefit.
Sources: B:report/sections/02_local.tex:234-239.

### EX073 Decoder-bound controller certificates
**Finite state.** Optional local controller invariant certificates bound to actual decoder; distinguish preservation from reachable initial states and all-cycle exclusion requiring ranking/SCC reasoning.
Sources: A:13.

### EX074 Shared generator templates
**DAG.** Consolidate Split/Gap generator proof templates while preserving public theorem names and intermediate cuts; generator maintenance rather than semantic circuit change.
Sources: A:11.

### EX075 Narrow modules and explicit audits
**Build architecture.** Thematic/light imports, preserve facade names, explicit affected Checks/Audit/checks targets beyond main umbrella; not new proof claim.
Sources: A:14-16.

