# Novelty audit and assumed prior baseline

Pinned repository: `7df43cdfacb490cd3ca3acd23e39027efebf8801`.

Complete file/ZIP member inventory and content hashes; all main manuscript section indexes inspected; proposal descriptions, shared exclusion catalogs, and relevant technical notes read; candidate-specific full-text searches across prose and proposed patches, excluding unchanged source snapshots from novelty matches. This is an overlap audit, not a fresh semantic certification of every prior implementation or a traversal of every historical link in incoming README.

Coverage records overlap; not a count of independent proposals. All statuses including notes-only/uncompiled/deferred/rejected alternatives are treated as prior.

## Scope

- 23 placed packets: `2026-10-26a` through `2026-10-26w`.
- All 5 incoming archives; 1042 archive members.
- 2329 inventoried files/member payloads; 2161 searchable text files.
- 175 overlapping coverage records.

Archive names and SHA-256 are recorded in `archive_manifest.json`; every placed file and incoming member is recorded in `prior_corpus_manifest.json`. Main manuscript heading locations are in `prior_report_sections.json`.

## Rejection rule

An implementation, renamed helper, another suggested client, or a compile check of an earlier idea is not a new proposal. Treat promised APIs as already available, even when the old packet only sketched them. A retained proposal must delete a different proof obligation, prove a materially different invariant, or remove a new dependency introduced after the old corpus. Broad advice about profiling, simp policy, imports, axiom audits, generators and finite certificates is methodology already covered.

## Candidate-specific screen

### Finite-ordinal order rigidity

**Target:** `WangTiles942PhysicalOrder.strictMono_fin_eq_self`. **Decision:** No matching proposal found; retain narrow local deletion.

**Nearest prior:** L05 finite invariant predecessor; L48 physical-position positive tail; FD07 internal strict order.

Strictly monotone finite selfmap is identity; this new finite-order rigidity proof is not supplied by those earlier contracts.

### Schema existential elimination

**Target:** `AnnotatedSchema.exists_separation_program_iff / AnnotatedReplacement.exists_program_iff`. **Decision:** Exclude generic mechanism; only a stronger schema-specific invariant could qualify.

**Nearest prior:** F01 exact object-formula specifications; L47 quadratic Boolean existential certificate; L21 schema index-map normalization.

Replacing witness construction by exists_eq_left/exists_and_left repeats an advertised binder-normalization mechanism.

### Native rank toNat from nonnegative blocks

**Target:** `NativeSourceMask.source_rank_four_blocks`. **Decision:** Exclude as standalone headline unless statement genuinely removes a global hypothesis.

**Nearest prior:** EX051 natural/integer rank bridge.

Shorter rank cast handling is explicitly prior; different local proof is not enough.

### Three-tap modulo-two kernel projection

**Target:** `CurrentWordCopies2011 and CurrentKernel2011`. **Decision:** Conditional: exact fixed-kernel sparse quotient invariant may survive; generic parity/carry does not.

**Nearest prior:** EX052 scalar decomposition/modular projection; L22 cyclic packing universal property; 2026-10-26o rejected reflected-parity/carry draft.

Must prove equality of the entire fixed kernel after reduction mod 2 before carry normalization and show additional consumers beyond previously advertised scalar projection.

### Nonzero integer as natural square-minus-one slack

**Target:** `ArithmeticNonzero.Rep.nonzero.correct`. **Decision:** No matching exact arithmetic proposal found; retain modest local idea.

**Nearest prior:** L47 Boolean slack elimination; L18 Euclidean canonical witnesses; L37 pairing canonical witnesses.

Uses integer discreteness and square positivity to eliminate sign case analysis in this distinct certificate; do not claim existential elimination generally.

## Coverage catalog

The EX001-EX075 and L01-L56 wording below is inherited, with attribution, from the structural-simplifications packet's audit/exclusions.json, itself cross-checking earlier packets. F01-F15 comes from that packet's freshness-exclusions.json. W, PA, IF, FD, RF and ST records are added by this review for the later manuscript proposals. These catalogs were used with current report headings and targeted source/notes review; they are not a substitute for checking new candidate overlap.

Historical aliases in inherited evidence map to current placements: P-a..P-f = a..f; I-deltas=o; I-round2=n; I-additional=m; I-eight=i; I-directions=j; I-ideas=k; I-six=l; I-roadmap=q; I-simplification=g; I-five=p; I-review=h; I-residual=r; Round3=v.

### EX001: Seven private optional-list-lookup inductions

Use List.mem_of_getElem? and List.getElem?_of_mem or mem_iff_getElem? at AnnotatedRename, Bound, ProofChecker, Assumption, RuleSide; wrappers or direct replacement.

Evidence: P-e:6; P-b:3; P-d:9.2; P-c:3; P-a:3.2.

### EX002: Option map injectivity

Replace AnnotatedParents judgment-code option case split by Option.map_injective judgmentCode_injective.

Evidence: P-e:6.

### EX003: Realizer and optimizer recursor congruence

Eliminate inner Nat.rec induction in PRCode.Realizes.prec, ScalarPRCode.Realizes.prec and ScalarPROptimizer.eval_optimize by explicit simp or shared axiom-free RecursorCore.rec_congr.

Evidence: P-a:3.1.

### EX004: Assignment naturality

Shared natAssignment composed with Sum.map and Expr.eval_rename for reindex/conjunction/disjunction/existsBlock; preserve expression fields and counts.

Evidence: P-b:4.1-4.2; P-d:2; P-c:4; P-a:3.3.

### EX005: Concatenated witness existential

Generic equivalence between Fin(m+n) witness and two Fin blocks via Fin.addCases, including zero lengths.

Evidence: P-b:4.1.

### EX006: Early witness-count projections

Move existing constructor count projection lemmas from RepresentationSize to constructors or lightweight module to avoid unfolding large data.

Evidence: P-b:4.3.

### EX007: Recursor iteration mechanics

Share fixed points, zero/done stability, successor-right/left and invariant or reject-or-good laws across five scanners and ContextLookup; keep executable Nat.rec definitions.

Evidence: P-e:7; P-b:5.2; P-d:5; P-c:9; P-a:8.1.

### EX008: Encoded-step semiconjugacy

Share typed/encoded iterator fusion and scan-list/table simulation from exact step_cons/terminal/reject laws; includes AnnotatedClosure coding/execution induction.

Evidence: P-e:7; P-b:5.2; P-c:9; P-a:8.1.

### EX009: Guarded-history fold

Share run_append, run_sound, Produces.append and Produces.step for Rename/Bound/ProofChecker with distinct Line/Judgment types and emit function.

Evidence: P-e:8; P-b:5.1; P-c:9.2.

### EX010: Explicit dynamic-seed PR iterator

Introduce iterateFrom with realized seed/fuel and parameterized step for scanner PR builders; preserve .val program and single expensive validator.

Evidence: P-b:5.3; P-c:9.3.

### EX011: Exact numeric Boolean reflection

Derive check=truth valid from 0-or-1 range and check=1 iff valid=true, then simplify Bound/Rename step_cons.

Evidence: P-e:8; P-b:5.4; P-a:8.2.

### EX012: Common tag threshold dispatcher

One arithmetic theorem for 0/1,2,3/4/5,6/7 and >=8 outcomes in BoundLocal/RenameLocal, over all natural tags.

Evidence: P-e:8; P-b:5.4.

### EX013: Carrier finite positivity enumeration

After fin_cases infer coordinate via hv _ in Carrier66.drop_pos/restore_pos instead of enumerating exact indices.

Evidence: P-e:3.

### EX014: Carrier canonical zero normalization

Replace canonical_zero unfold/rw/ring by narrow simp using canonical equalities.

Evidence: P-e:3.

### EX015: Integer units

Use Int.eq_one_or_neg_one_of_mul_eq_one in ShortSystem.unit_eq_one and reuse uniformly in product_eq_one_iff with sign exclusions.

Evidence: P-e:4.

### EX016: Five residual squares

ShortSystem.residualSum_zero_iff via nonnegative-add/square-zero lemmas or Finset.sum_mul_self_eq_zero_iff rather than repeated nlinarith.

Evidence: P-e:4; P-f:report/sections/02_local.tex:55-104; P-a:4.1.

### EX017: Common executable residual aggregation

Share eval_sumExpressions/sumSquares zero iff, degree <=2d and parameterized (b+1)*length cost bound across DAGQuartic, NaturalDAGQuartic, QuadraticRegisterSystem, QuarticCost.

Evidence: P-b:6.1; P-d:8.1; P-c:10; P-a:4.2.

### EX018: Shared semiring gate induction

Extract GatesSyntax/data below generic semiring soundness/completeness then derive natural/integer compiler theorems without import cycle.

Evidence: P-b:6.2; P-d:8.3.

### EX019: Merge identical constructor branches

QuarticCompiler.Gates.complete add/mul proof alternatives share one branch.

Evidence: P-e:5.

### EX020: Move syntax degree and rename laws earlier

Canonical Expr polynomial_rename, syntaxDegree/polynomial_degree_le at expression layer; weighted degree at constant weight one; keep cancellation-aware normal forms.

Evidence: P-b:6.2; P-d:8.2; P-a:7.2.

### EX021: Generic RHS degree interface

Share DAGQuartic/NaturalDAGQuartic node RHS degree <=2 from wire degree <=1 and small degree add/sub helpers.

Evidence: P-e:11.

### EX022: Shorter run_map induction step

Use map_append/map_singleton/Node.eval_map directly at recursive boundary in ArithmeticDAG.run_map.

Evidence: P-e:5.

### EX023: Cast Pell conclusion as a whole

Replace FirstPellCarrier.first_norm_facts_int final disjunction split by exact_mod_cast hgap, retaining lifts and divisibility guards.

Evidence: P-e:5.

### EX024: Shared DivMod certificate

One neutral arithmetic certificate_iff for QuadraticDivMod/RegisterDivMod; retain separate realizers and witness counts 1/23.

Evidence: P-e:6.

### EX025: Identical scalar tail

Extract SplitNinePolynomial59/GapNinePolynomial66 ratioValue with common map/cast laws and aliases; keep recipe exponents and b factor distinct.

Evidence: P-e:9; P-c:8.

### EX026: Identical 99-node free-carrier tail

Common boundary-port block for Split 416..514 and Gap 385..483 under reference renaming; prove embedding and common ratioValue semantics, no copy gates.

Evidence: P-c:8.

### EX027: Guarded solution transport

HasSolution(D,P) congruence/composition via two existential directions, not assignment bijection; Current69/70/71 same-domain examples.

Evidence: P-e:10.

### EX028: Nine-coordinate existence packaging

Parameterize evaluator to share SplitSourceExistence/GapSourceExistence66 positive/natural coordinate existential proofs; slot7 unshifted internally.

Evidence: P-f:report/sections/03_architecture.tex:11-67.

### EX029: Named conjunction accessors

Derived Canonical.Z_eq_delta/index_eq_one/rank_pos and PortBounds/core positivity accessors without changing conjunction definition.

Evidence: P-f:report/sections/03_architecture.tex:68-98.

### EX030: Coherent restored source and scalar window

One actual source assignment and positive N yielding both low/high mask tests, shared Carrier65->66 restoration and radix power normalization.

Evidence: P-f:report/sections/03_architecture.tex:99-146; P-a:source_notes/digits-review.md:8.

### EX031: Base interface below completeness

CurrentCarrierBase2011 below ThirteenCarrierComplete, old facade retained, simpler digit clients redirected.

Evidence: P-f:report/sections/03_architecture.tex:147-171.

### EX032: Parameterized Split/Gap degree profile

Share source positivity/domination and optional upper packing bound with exact degree gaps, leading coefficients and concrete sharp exponents.

Evidence: P-f:report/sections/03_architecture.tex:172-213.

### EX033: Finite row envelope proof schema

Replace NativeCoefficientBounds 22 row proofs with shared positivity/sign basis, abs_ite_le traversal and restricted linarith; preserve sharp transport dependence.

Evidence: P-d:3; P-c:6.

### EX034: Finite coefficient catalog or majorant

Encode 25 values or sparse coefficient vectors over nonnegative monomial basis; checked table/evaluation equality derives original sharp envelope.

Evidence: P-d:3.3; P-c:6.2.

### EX035: Coefficient homomorphism compression

Focused simp/generated finite-case tactic or single computable ring AST for Native/Gap mapRowCoefficient families; preserve authoritative table, CommRing and support.

Evidence: P-f:report/sections/03_architecture.tex:214-253; P-c:6.1.

### EX036: Sparse row equality checker

Small normalized sparse quadratic syntax for Split/Gap/Native source-row identities, linked to independent recipe; not full finalizer expansion.

Evidence: P-c:12.3.

### EX037: Elementary row operations

One addAt zero-set equivalence and surjective reindexing theorem for SplitCertificate59 transformed_zero_iff; preserve distinct source/destination.

Evidence: P-c:13.

### EX038: Existing run_power certificate

Emit one actual-node exponent label table and PowerStep certificate, specialize run_power, retain all 193 named powers; shard if needed.

Evidence: P-e:11; P-f:report/sections/04_circuits.tex:50-127; P-b:7.2; P-d:7.2; P-a:5.1.

### EX039: Indexed node equation facade

Shared per-circuit natural_step/run_node_equation helper or demand-driven generated specialization for 999 node facts; keep valuable cuts/public aliases.

Evidence: P-e:11; P-f:report/sections/04_circuits.tex:128-166; P-b:7.3; P-d:7.1; P-a:5.2.

### EX040: Generator respects semantic cuts

Split sourceSRegister/sourceRankRegister use already proved high/S/T/block identities; snapshot cuts dictionary in generator to avoid later/self references.

Evidence: P-c:7.

### EX041: Shared topological invariant

One indexed run_invariant strong induction for uniqueness, degree and nonnegativity, instantiating existing node equations/topology.

Evidence: P-c:11; P-a:6.

### EX042: Commutative node relation and translation

Extend NodeRel with swapped add/mul, keep subtraction ordered; generic Split/Gap positive-natural simulation with prefix/reference/exception facts.

Evidence: P-c:12.1; P-a:7.1.

### EX043: Local append invariants

Share NaturalRegisterProgram.push topology/allowed old-vs-last index splits and eval_old/eval_last append bookkeeping.

Evidence: P-a:7.3.

### EX044: Semantic block certificates

Local symbolic value tables/recipe tail proofs linked to full existing DAG and output; retain independent high-level recipe and cutpoints.

Evidence: P-e:11; P-f:report/sections/04_circuits.tex:167-187.

### EX045: Shared ShortSystem degree prefix

Factor exact 224-line common prefix of literal/compact degree proofs or existing degree checker with two tails, retaining <=68 and value bridges.

Evidence: P-f:report/sections/04_circuits.tex:188-210.

### EX046: Checked or dependent circuit views

Bundle list/topology/bounded output or SafeNode operands Fin earlier with exact erasure equality; not new arithmetic circuit.

Evidence: P-f:report/sections/04_circuits.tex:211-233.

### EX047: Half-radix identity

Derive (sa)%(2s)+(sb)/(2s)=s*(a%2)+b/2 for s>0; bound/parity replace NativeCyclicRotation enumeration.

Evidence: P-b:8.1; P-d:4.1; P-c:5; P-a:9.2.

### EX048: Shared full-modulus residues

Low-level cyclic addition/subtraction and aligned arbitrary-shift normal forms, support-zero and off-origin mask lookup across current/legacy modules.

Evidence: P-e:12; P-f:report/sections/02_local.tex:176-209; P-b:8.2; P-d:4.2; P-a:source_notes/digits-review.md:5.

### EX049: Weaken reflected residue modulus

CurrentEarlyPadding reflected_mod_sixteen from CurrentClause reflected_weight_mod modulo2048 via ModEq.of_dvd; identical selector definitions.

Evidence: P-b:8.2; P-c:15; P-a:9.1.

### EX050: Decode source-register equations once

Shared q=1+Jβ,L=q²−1,N=q³,X=qw from literal rows for NativePellBootstrap/Power; separate positivity/rank/port bounds.

Evidence: P-b:8.3.

### EX051: Natural integer rank bridge

Shared nativeRank.toNat cast equality/nonnegativity/lower bounds from actual positive source in NativePellFirstIndex and source-window proofs.

Evidence: P-c:notes/arithmetic.txt:6.

### EX052: Scalar decomposition API

From raw=d+Bq derive quotient under d<B, residue when m divides B, and zero carry under raw<B; no unwarranted digit premise on residue/reset.

Evidence: P-e:12; P-a:9.4.

### EX053: Derived recurrence and small facts record

CarryCertificate/WordFacts or smaller view of existing Facts; recurrence derives from digit bound+decomposition; source/word/mask layers distinct.

Evidence: P-e:12; P-b:9.1; P-d:9.1; P-c:15; P-a:9.4.

### EX054: Conditional padding witness

Move existence of padding u inside middle-phase implication to remove dummy zero witness in CurrentCount2011 caller.

Evidence: P-a:9.3.

### EX055: Finite fiber pushforward

One sum_fiber_mul identity for mass_foldStencil, convolution_foldStencil and word_foldStencil; allow collisions, retain modular power reasoning.

Evidence: P-d:6.

### EX056: Origin decrement word

word_sub_origin with delta<=a 0 for CurrentHighDigits/NativeHighPort54 high_mask_word; preserve no-borrow hypothesis.

Evidence: P-a:source_notes/digits-review.md:6.

### EX057: Direct physical selector sum

Expose selectorCount equality to physical Fin942 sum before prefix conversion; CurrentOneHot/FieldOffsets use direct equality.

Evidence: P-a:source_notes/digits-review.md:7.

### EX058: Chunk dispatch and sum assembly

WangTiles942Data adjacent-block/balanced or Euclidean dispatcher, final partial block; CurrentKernel finite-sum tree; retain checked leaves.

Evidence: P-e:13; P-b:9.2.

### EX059: Copied-field direction descriptor

One copiedFields_bounded or finite west/north/east/south descriptor for four control field offset/width/packed shifts; preserve tuple-order difference and collisions.

Evidence: P-e:13; P-b:9.3.

### EX060: Optional mask block library

Reuse lookup/length/bound facts for second mask client; preserve low +1, high origin -1 and scalar beta shift distinctly.

Evidence: P-e:13.

### EX061: Shared direct/native graph builder

Parameterize rawStepProgram/boundedRunProgram over small combinator record, retain native/direct realizers and exact costs 1742/6924.

Evidence: P-e:14.

### EX062: All-model sealed completeness bridge

Centralize axioms_of_zfc_model extraction, semantic validity and seal_valid before completeness; retain universes, arbitrary/nonstandard models and contexts.

Evidence: P-b:10.1; P-c:14; P-a:10.2.

### EX063: Arity-polymorphic closed transport

Generalize ObjectQuarticCompiler local closed helper to any Fin n, reuse at target arity or expose sat_noZeroForm_at_iff.

Evidence: P-b:10.2; P-c:14.1.

### EX064: Definable induction transport

omega_ind_of_spec takes actual formula/environment/Sat equivalence; shares semantic transport, not unrestricted external predicate induction.

Evidence: P-a:10.1.

### EX065: Existing internal semiring interfaces

Share only model-independent index/renaming or row-conjunction facts between ObjectQuadraticSystem/QuadraticRegisterComposition; preserve unguarded evalRel_unique.

Evidence: P-d:8.4; P-c:14.2.

### EX066: Specialize half_base_bound_31

SelectiveCoefficientBounds specialization m=31 directly via half_base_bound and existing equality hypothesis.

Evidence: P-f:report/sections/02_local.tex:10-54.

### EX067: Use Finset intersection

LowMaskCoding.sum_range_support and MultiTargetCarry.selectedMask_eq via filter_mem_eq_inter/inter_eq_right rather than ext membership proof.

Evidence: P-f:report/sections/02_local.tex:105-144.

### EX068: Predecessor exponent cancellation

Seven hpow bodies use pow_succ' and Nat.sub_add_cancel ht instead of congr+omega; avoid double-counting deleted half_base specialization.

Evidence: P-f:report/sections/02_local.tex:145-175.

### EX069: Convolution distributivity tail

NativeCyclicConvolution.word_convolution final factorization via sum_mul/mul_sum/pow_add and controlled AC simplification.

Evidence: P-f:report/sections/02_local.tex:216-222.

### EX070: Exact two-power lower bound

NativeRadixDigits hr via Nat.one_lt_two_pow instead of weaker bound+normalization+omega.

Evidence: P-f:report/sections/02_local.tex:223-228.

### EX071: FiniteSwitch boundary normalization

ArithmeticFiniteSwitch non-equality branch tag<count+1 iff tag<count eliminates redundant case split.

Evidence: P-f:report/sections/02_local.tex:229-233.

### EX072: cellDigit_lt branch expansion

Optional split_ifs/norm_num replacing existing highDigits_lt specialization; report recommends retaining original unless measured benefit.

Evidence: P-f:report/sections/02_local.tex:234-239.

### EX073: Decoder-bound controller certificates

Optional local controller invariant certificates bound to actual decoder; distinguish preservation from reachable initial states and all-cycle exclusion requiring ranking/SCC reasoning.

Evidence: P-e:13.

### EX074: Shared generator templates

Consolidate Split/Gap generator proof templates while preserving public theorem names and intermediate cuts; generator maintenance rather than semantic circuit change.

Evidence: P-e:11.

### EX075: Narrow modules and explicit audits

Thematic/light imports, preserve facade names, explicit affected Checks/Audit/checks targets beyond main umbrella; not new proof claim.

Evidence: P-e:14-16.

### L01: Exact recursive decoder graph

Fuse quote recovery and depth into one induction; use Option.bind_eq_some_iff to skip impossible failure branches; derive exact arbitrary-code/fuel iff and monotonicity. Separate successful-branch cleanup is also prior.

Evidence: I-eight: Describe the tree decoder by its exact graph; I-directions: Fuse syntax-decoder correctness; I-review: decoder section; I-round2: 04_decoder.tex

### L02: Total decoding for parent checker

Use decodeTable_total and tableCode_of_decode to rewrite any raw parent list to a typed list, then apply check_lists. No re-encoding induction.

Evidence: I-round2: 03_parents.tex

### L03: Exact rational witness descent

Take the existing rational root to its integer numerator by denominator-one power lemma; preserve sign and all joint equations; share general separated norm reconstruction below both finalizers.

Evidence: I-eight: Preserve rational roots; I-additional: Preserve the exact rational root

### L04: Whole-product unit decomposition

Use IsUnit.mul_iff and Int.isUnit_iff once for all factors, resolving conditional sign exclusions without manufacturing complementary products.

Evidence: I-eight: Decompose the product's units once

### L05: Finite invariant predecessor/reflection

Restrict an injective finite map to a forward-invariant predicate and obtain a predecessor by surjectivity. Offset-19 exclusion avoids full orbit arithmetic.

Evidence: I-eight: Use finiteness to recover an invariant predecessor; I-six: Idea 6

### L06: Degree before support

Bound natDegree of factors and product, then infer coefficient vanishing. Avoid expanded nested coefficient sums in SelectiveCarry.

Evidence: I-eight: Prove the support envelope before individual coefficients

### L07: Point-mass rotation

Specialize existing word_convolution at Pi.single t 1; derive rotation congruence without another reindexed exponent sum.

Evidence: I-eight: Rotation is convolution with a point mass

### L08: Primrec compositional automation

Register extensional Primrec and closure rules for fun_prop; synthesize formula-constructor proofs without changing explicit PR programs or costs.

Evidence: I-eight: Automate extensional primitive-recursiveness composition

### L09: Canonical digit/carry normalization

Maximum principle proves carry uniqueness with raw vector and digits fixed; fixed-length ofDigits injectivity derives digits from equal full words; canonical window normalization follows only after strict representative is fixed.

Evidence: I-eight: Canonical normalization from a finite maximum principle

### L10: Signed modular relation

Compose congruence up to sign using symmetry/transitivity/multiplication/powers and natAbs bridges; guarded half-interval uniqueness is also in notes.

Evidence: I-directions: Treat Pell sign ambiguity; I-ideas: Make congruence up to sign compositional; I-additional: Compose congruence up to sign

### L11: Internal tagged views and unique existence

One constructor-view theorem replaces BoundStep disjunction inversions, and one definable internal ∃! induction replaces separate totality/uniqueness. Preserve nonstandard codes.

Evidence: I-directions: Constructor views and one internal unique-existence induction

### L12: Internal recursive-graph laws

Prove ThetaG preservation and fusion using totality, functionality and explicit definability of stage invariants; addition, multiplication and closure are clients.

Evidence: I-directions: Preservation and fusion for internal recursive graphs

### L13: Depth-budget interpreter

Baseline/excess max-plus certificates recover GraphRep depth bounds, with local adapters, AST traversal, let-sharing and memoization; factorial/product plans supplied.

Evidence: I-directions: Synthesize representation-depth bounds with small certificates

### L14: Closed cyclic carry formulas

Rotated weighted sums give least/greatest carries, exact one/two-solution classification and budget-selected least witness. Explicit construction and uniqueness are prior.

Evidence: I-directions: An optional structural alternative: explicit cyclic carries

### L15: Zero-or-singleton finite support

Use Finset.sum_le_one_iff for all-zero or one selected index; preserve the empty type case.

Evidence: I-ideas: Use the existing finite-support classification; I-round2: 05_finite_and_cycle.tex; I-simplification: Use the existing sum-at-most-one API

### L16: Pell parity reuse

Invoke SignedPellResidue.odd_index_of_base_dvd in NativePellStepDown and delete unused local positive-index proof.

Evidence: I-ideas: Reuse the already proved Pell parity criterion; I-six: Idea 2; I-additional: Reuse the existing odd-index theorem

### L17: Pairing inverse-graph projections

Eliminate a coordinate of forward graph via product equivalence; normalize Fin witnesses then consume existing certificate iff. Includes quadratic pairing/tree graphs and prospective Cantor application.

Evidence: I-ideas: Derive inverse graphs from a product equivalence; I-additional: pairing graph section

### L18: Euclidean certificate uniqueness

Share positive-denominator quotient/remainder/slack certificate and identify all its witnesses; extend coherence to composed witnesses.

Evidence: I-ideas: Share the positive-denominator Euclidean certificate and further questions

### L19: Affine composition budget

One witness/depth potential pays composition overhead, including coefficient-six Thin invariant, aggregate child witnesses, and direct-versus-indirect zero-arity distinction.

Evidence: I-ideas: Factor the arithmetic budget behind composition

### L20: Support-restricted evaluator/frame rules

Propose support-only evaluator congruence and overwrite/frame lemmas; notes acknowledge existing WitnessCompaction.eval_congr. Notes-only still excluded.

Evidence: I-directions: evidence/prior_ideas.md candidate 7

### L21: Schema index-map normalization

Normalize rsep/rf1/rf2/ri renaming chains through algebra of index maps in AnnotatedSchemaMaps. Notes-only still excluded.

Evidence: I-directions: evidence/semantic_review.md section 5 and evidence/prior_ideas.md candidate 8

### L22: Cyclic packing by universal property

Represent word packing as monoid-algebra hom into ZMod(radix^n-1); deduce convolution/product and rotation/monomial laws. Notes-only still excluded.

Evidence: I-directions: evidence/algebra_review.md final optional direction and evidence/prior_ideas.md candidate 9

### L23: Delete unused internal inductions

Use nat_zero_or_succ for ObjectAdditionCancellation.addRel_zero_iff and ObjectNaturalZero.mulRel_zero_iff when successor branches never use induction hypotheses; remove private stage formulas.

Evidence: I-six: Idea 1; I-roadmap: Delete internal inductions whose hypotheses are unused

### L24: Abstract signed divisibility witnesses

Use closure of divisibility under subtraction/negation and existing ModEq conclusions instead of extracting and reconstructing witnesses for signed endpoints.

Evidence: I-six: Idea 3

### L25: Pell base monotonicity

Compare bases via positive pair recurrence and simultaneous x/y monotonicity, removing exponential detours in main_index_gt_first. Actual value gap is enough for index comparison.

Evidence: I-six: Idea 4; I-residual: Compare Pell bases through the positive pair recurrence

### L26: Integer-domain norm proof

Prove norm_ne_zero_of_not_isSquare wholly over integers using square/divisibility facts; avoid rational squarehood detour.

Evidence: I-six: Idea 5

### L27: Negative Pell from positive units

Square a hypothetical negative-norm solution, classify positive unit powers, and use their first-coordinate congruence to contradict norm -1.

Evidence: I-roadmap: Derive the negative Pell obstruction from positive units

### L28: Normalize residue obstructions

Reduce multiple three-residue norm obstructions to the existing shifted ShortEquation.strong_ne_neg_one theorem; one shared discriminant normal form.

Evidence: I-roadmap: Normalize three residue obstructions to one existing theorem

### L29: Minimum saturation

Use equality of a sum with the sum of heterogeneous lower bounds to obtain every block equality, including coupled nonzero minima in MinimumNorm.minima76_zero_iff.

Evidence: I-roadmap: Extract all block equalities from one minimum-saturation theorem

### L30: Monotone local-certificate closure

One calculus for empty/union/insert certificates over arbitrary internal set carriers, deriving repeated BoundClosed constructors and naturalness.

Evidence: I-roadmap: Optional: a calculus for monotone local certificates

### L31: Scale-parametric Pell ratio estimate

General real error factor covers upper_estimate and upper_estimate_scaled through the same proof; old interfaces become specializations.

Evidence: I-five: A: one Pell estimate with an explicit error factor

### L32: Natural perturbation and power sandwich

Replace analytic perturbed powers with natural-number inequality and transfer through Pell growth bounds; expose separate error budget instead of stronger global threshold.

Evidence: I-residual: A natural-number perturbation kernel for both Pell upper bounds

### L33: Exact half-binomial quotient

Identify lower binomial block as remainder, then recover half-binomial value via exact integer half-quotient rounding under one error inequality.

Evidence: I-residual: Recover the half-binomial value through an exact integer quotient

### L34: Arbitrary-premise fragments

Collect any list of proof fragments with suffix-history-length parent indices and finish the rule once; preserve reversed history convention and derive old arity wrappers.

Evidence: I-five: B: construct proof fragments for any number of premises

### L35: Successor-indexed fork certificate

State ForkCertificate(out+1) equivalence first, then isolate impossible zero once; avoid natural predecessor cancellation in each branch.

Evidence: I-five: C: prove fork certificates at successors first

### L36: Projected support-difference separation

Under additive projection, displacement outside S-S forces one supported factor to vanish; used with actual native support and existing no_difference_606.

Evidence: I-five: D: separate supports through a quotient homomorphism

### L37: Canonical square-pairing auxiliary witnesses

Characterize selector, slack and max witnesses as well as output pair code; full row equivalence gives deterministic existing witnesses.

Evidence: I-five: E: pairing certificates have canonical witnesses

### L38: Shared executable and semantic rule schedules

Define ordered tag/rule schedule syntax once, interpret as Boolean validity and PR computation, and certify erasure to existing frozen programs.

Evidence: I-residual: Define rule schedules once and derive both interpretations

### L39: Direct South prefix use

Apply binaryWord_prefix at (1,8) and (2,7) then normalize addresses inside lambdas; eliminate redundant function equalities for offsets19/20.

Evidence: I-round2: 06_south_prefix.tex; I-deltas: pageheading 4

### L40: Hoist binary word congruence

Move existing binaryWord_congr to definition layer; horizontal_words and copy_word_translation no longer reopen finite sums.

Evidence: I-round2: 07_word_congruence.tex

### L41: Cycle reachability reuse

Use theta a.val b as exact difference-cell witness, and derive zero-base propagate from propagate_from; no new coordinate abstraction.

Evidence: I-deltas: pageheading 5; I-round2: 05_finite_and_cycle.tex

### L42: Boundary high-color fibers

Guarded equality-indexed North/South fibers, or NorthView by color, replace repeated eliminations in eight boundary classifiers while keeping literal initializer/seam tuples.

Evidence: I-deltas: pageheadings 6–7; I-round2: 08_north_view.tex

### L43: Selector assignment coherence

Characterize alternate assignment from selected bits in the same original word and inverse coordinate; transport facts_marked_word by resulting equality.

Evidence: I-deltas: pageheading 8

### L44: Explicit CRT congruence transport

Replace gcongr/exact? in BoundedForallCertificate with add_right/mul_right/add_right applied to the existing congruence witness.

Evidence: I-round2: 09_supplemental.tex S1

### L45: Binary composition depth helper

Factor Fin2 elimination in five BoundedForallDepth wrappers, preserving h+8 bounds; charge support overhead.

Evidence: I-round2: 09_supplemental.tex S2

### L46: Small-ordinate Pell fundamental criterion

Use classification of fundamental-unit powers to prove any positive solution with y≤3 is fundamental; criterion sharp at y=4.

Evidence: I-additional: A uniform small-ordinate criterion for Pell minimality

### L47: Quadratic Boolean existential certificate

Consume exists_zero_certificate_iff before conditional branching; eliminate slack via existential/conjunction rearrangement, preserving whole Rep data.

Evidence: I-additional: Consume the Boolean certificate before constructing a conditional

### L48: Physical-position injectivity by positive tail

Recognize physicalPosition as Fin.cons zero positive strictRank-tail, invoke Fin.cons_injective_iff and compose existing injections.

Evidence: I-additional: Optional: recognize the physical permutation as a positive tail

### L49: Finite-word representation boundary

Unify ZMod/Fin/List.ofFn and finite-sum conversion; geometry wrapper for range and wrap facts; distinct from proving a new packing theorem.

Evidence: I-review: Unify modular and finite-word interfaces

### L50: Decoder codec left inverse

Shared parse-then-check and decoder left-inverse→quote injectivity; successful Option bind destructuring is explicit in earlier reports.

Evidence: I-simplification: Reuse parser and list infrastructure; I-review: Shorten decoder proofs

### L51: Full invertible row transformations

General invertible linear row combinations are already mentioned as a later extension to elementary row-addition zero-set invariance.

Evidence: P-c: Represent elementary row operations once

### L52: Sum-index witness regrouping

Use Sum.exists_sum plus one cast identity for Sum.rec to regroup DAG input/witness valuations; preserve topology/output/Allowed guards.

Evidence: I-review: evidence/structural/findings.txt section 3

### L53: Dedicated natural evaluator option

A natural-semiring evaluator with erasure-correctness to ArithmeticDAG is already proposed as an optional alternative to repeated casts/positivity.

Evidence: I-review: evidence/structural/findings.txt section 7

### L54: Guarded binary/unary constructor witnesses

Move binaryForm/unaryForm early and share code_binaryForm, renamed_binaryForm and bound_binaryForm, avoiding repeated three-tag witnesses in Rename/Bound soundness.

Evidence: I-review: evidence/syntax/findings.txt section 6

### L55: Pair-zero and degree-renaming consolidation

Publish zero_pair once for three annotated modules and reuse expression syntaxDegree_rename; these local algebra cleanups are notes-only but explicit.

Evidence: I-review: evidence/syntax/findings.txt section 7

### L56: Replace artificial existential lets

Use set ... with equality in NativeHalfBinomial.upper_estimate_scaled instead of obtaining trivial existential witnesses. This readability change is already proposed.

Evidence: I-review: evidence/arithmetic/findings.txt section 8

### F01: Compositional exact object-formula specifications

Normalize selected Sat clauses, atom specs, scons and determined existential witnesses; retain structural expression induction but combine add/mul semantic cases.

Evidence: 2026-10-26s/report.tex, sections Normalize exact object-formula specifications compositionally (177–290).

### F02: Pell comparison through positive scale/error envelope

Share scaled upper and lower ratio comparisons across ordinary and native clients, preserving denominator normalization; parameterized error allowance and wrappers are prior.

Evidence: 2026-10-26s/report.tex291–384;2026-10-26u/report.tex125–197.

### F03: Integer recovery from two error budgets

Use Nat.floor_eq_iff to identify natural integer parts from two strict intervals with nonnegative offset and total error ≤1; half-binomial,ordinary and variable-denominator clients.

Evidence: 2026-10-26s/report.tex385–442; examples/IntervalExtraction.lean.

### F04: Closure of observed internal certificate sets

Abstract internal-set union/insertion closure via monotone step predicates and injective observation encoding; bound,renaming and rank clients; malformed unobserved members allowed.

Evidence: 2026-10-26s/report.tex443–517; examples/ObservedClosure.lean and ClosureClients.lean.

### F05: Exact list codec and typed parents via raw checker

Identify concrete encodeNatList with standard Encodable list codec, reuse its length theorem, derive typed parent correctness by encoding through raw correctness.

Evidence: 2026-10-26t/report/sections/02_encoding.tex.

### F06: Local coefficient fiber as foundational theorem

Isolate one selected pair-sum exponent without global Sidon assumptions; handle diagonal/off-diagonal multiplicities, mixed products, and derive separated rows through selective-zero results.

Evidence: 2026-10-26t/report/sections/03_coefficients.tex;07_next.tex mixed products.

### F07: Absolute second-coordinate Pell minimality

Replace signed y enumeration by |y| and y², use the consecutive-square gap, and optionally derive fundamentality from minimal y² among competitors with x>1.

Evidence: 2026-10-26t/report/sections/04_pell.tex; optional/PellMinimum.lean.

### F08: First failure with its valid prefix

Package least bounded departure and all earlier predicate instances; retain separate geometric endpoint/nonexistence premises in InitialStrip left/right clients.

Evidence: 2026-10-26t/report/sections/05_first_exit.tex;2026-10-26u/report.tex320–352.

### F09: Stronger common native-rank envelope

Use positive transport gap to prove (2q−1)(q²−1)≤R for q≥3; derive R≥40 and R>3q from one nonlinear proof, with original public wrappers.

Evidence: 2026-10-26u/report.tex198–269.

### F10: Integer interval induction centered at the seed

Replace two Nat inductions/toNat distances by translated Int.induction_on or arbitrary-center Int.inductionOn'; preserve strict interval motive and discuss choice-axiom tradeoff.

Evidence: 2026-10-26u/report.tex270–318; patches/optional/interval-propagation-centered.patch; Round3::LeanReview3/report/sections/06_interval.tex.

### F11: Shared-edge construction and paired spatial pulse

Build west(x)=E(x−1),east(x)=E(x) with pulse at min(old,new); preserve unconditional statements by overwriting state with supplied q; prove direct stepTile bridge and/or paired edge invariant once.

Evidence: 2026-10-26u/report.tex353–438,lean/SharedEdgeRow.lean;Round3::LeanReview3/report/sections/07_pulse.tex.

### F12: Absolute-value trace-bound API reuse

Turn t≤|x| directly into the exterior disjunction through le_abs'; retain inclusivity and halted/write-before-move behavior.

Evidence: 2026-10-26u/report.tex440–449;Round3::LeanReview3/report/sections/05_machine.tex M3.

### F13: Sentinel-last state encoding injectivity

Identify none-at215 stateNumber with finSuccEquivLast.symm followed by Fin.val, then compose existing injectivity.

Evidence: Round3::LeanReview3/report/sections/04_encoding_action.tex E1.

### F14: Reflect action halt through state-number injectivity

Rewrite equality through stateNumber_injective.eq_iff, act_stateNumber and stateNumber_none; keep target<216 bound.

Evidence: Round3::LeanReview3/report/sections/04_encoding_action.tex M1.

### F15: Split machine color proof only at write site

Use one-cell tape write support/frame rule; leave moved-head conditional symbolic away from old head instead of splitting destination again.

Evidence: Round3::LeanReview3/report/sections/05_machine.tex M2.

### W01: Helical period as lattice vector

Use translation periods on integer pairs to eliminate bilateral induction, including seam status.

Evidence: 2026-10-26w/report.tex

### W02: Refined-pair polynomial identity before evaluation

Replace complex-square-root detour with a universal algebraic identity, then specialize.

Evidence: 2026-10-26w/report.tex

### W03: Twisted-band coordinate equivalence

One finite coordinate equivalence supplies exact normalization and existence for twisted bands.

Evidence: 2026-10-26w/report.tex

### W04: Matching rows from shared edge fields

Store shared horizontal edge once and establish literal operating/initializer constructor equalities.

Evidence: 2026-10-26w/report.tex

### PA01: Direct wall finite bounds

Use Fin 3 bounds and power monotonicity in new head-wall proofs.

Evidence: Lean_Proof_Simplification_Post_Adoption_2026-10-26.zip::report/01-summary.tex,06-causality.tex,07-canonical.tex,08-accounting.tex

### PA02: Actual receiver causality

Every actual receiving tile lies at the moved head using spatial matching only, retaining halt target 215.

Evidence: Lean_Proof_Simplification_Post_Adoption_2026-10-26.zip::report/01-summary.tex,06-causality.tex,07-canonical.tex,08-accounting.tex

### PA03: Extraction/construction whole-tile coherence

An arbitrary actual matching encoded row equals independently constructed stepTile in the open strip.

Evidence: Lean_Proof_Simplification_Post_Adoption_2026-10-26.zip::report/01-summary.tex,06-causality.tex,07-canonical.tex,08-accounting.tex

### IF01: Helical periodic orbit

Normalize signed helix iteration through periodic integer orbits.

Evidence: ProveIt_Additional_Lean_Simplifications_2026-10-26.zip::diophantine-lean-proof-interfaces-2026-10-26/report/report.tex

### IF02: Coprime divisibility without witnesses

Use coprime cancellation at divisibility interface and preserve degenerate cases.

Evidence: ProveIt_Additional_Lean_Simplifications_2026-10-26.zip::diophantine-lean-proof-interfaces-2026-10-26/report/report.tex

### IF03: Geometric bound from exact identity

Obtain upper geometric estimate from existing exact sum identity rather than induction.

Evidence: ProveIt_Additional_Lean_Simplifications_2026-10-26.zip::diophantine-lean-proof-interfaces-2026-10-26/report/report.tex

### IF04: Positive quadratic margin as interval

Turn positive margin into an interval via ordered algebra rather than explicit contradictions.

Evidence: ProveIt_Additional_Lean_Simplifications_2026-10-26.zip::diophantine-lean-proof-interfaces-2026-10-26/report/report.tex

### IF05: Signed-borrow prefix meaning

Give finite signed borrow an exact integer prefix identity, with old nonnegative result as corollary.

Evidence: ProveIt_Additional_Lean_Simplifications_2026-10-26.zip::diophantine-lean-proof-interfaces-2026-10-26/report/report.tex

### IF06: Native ranks through one scalar coordinate

Factor affine rank variation through a scalar, preserving information lost by that projection.

Evidence: ProveIt_Additional_Lean_Simplifications_2026-10-26.zip::diophantine-lean-proof-interfaces-2026-10-26/report/report.tex

### FD01: Span cutoff before support cases

Use span lower bound to exclude most support cases in sparse coefficient proof.

Evidence: diophantine-lean-further-deltas-2026-10-26.zip::diophantine-lean-further-deltas-2026-10-26/report/report.tex

### FD02: Two-dimensional helix period

Replace helix signed induction with period subgroup algebra.

Evidence: diophantine-lean-further-deltas-2026-10-26.zip::diophantine-lean-further-deltas-2026-10-26/report/report.tex

### FD03: Period lower bound from strip width

Derive geometric period bound from independent strip constraints.

Evidence: diophantine-lean-further-deltas-2026-10-26.zip::diophantine-lean-further-deltas-2026-10-26/report/report.tex

### FD04: Pairing branch from output shell

Read branch from threshold inside each square shell, then only two cases remain.

Evidence: diophantine-lean-further-deltas-2026-10-26.zip::diophantine-lean-further-deltas-2026-10-26/report/report.tex

### FD05: List-head bound from constructor

Use constructor equation directly instead of generic encoding inequality work.

Evidence: diophantine-lean-further-deltas-2026-10-26.zip::diophantine-lean-further-deltas-2026-10-26/report/report.tex

### FD06: Geometric sums without local induction

Use existing geometric sum formula and derive upper bound directly.

Evidence: diophantine-lean-further-deltas-2026-10-26.zip::diophantine-lean-further-deltas-2026-10-26/report/report.tex

### FD07: Internal order from strict part

Construct internal linear order from strict-order laws, preserving definitional compatibility.

Evidence: diophantine-lean-further-deltas-2026-10-26.zip::diophantine-lean-further-deltas-2026-10-26/report/report.tex

### FD08: Direct Sidon polarization

Use direct polarization of equal sums and squares in Sidon uniqueness argument.

Evidence: diophantine-lean-further-deltas-2026-10-26.zip::diophantine-lean-further-deltas-2026-10-26/report/report.tex

### RF01: Formula threshold by constructor minima

Derive code lower threshold from constructor minima with exact constructor monotonicity.

Evidence: diophantine-lean-proof-refinements-2026-10-26.zip::diophantine-lean-proof-refinements-2026-10-26/report/lean-proof-refinements.tex

### RF02: Object algebra before successor discreteness

Use nonzero additive difference for strict multiplication, move semiring before Boolean roots/discreteness.

Evidence: diophantine-lean-proof-refinements-2026-10-26.zip::diophantine-lean-proof-refinements-2026-10-26/report/lean-proof-refinements.tex

### RF03: Period-one functions

Use constant period-one orbit to eliminate helix/seam induction.

Evidence: diophantine-lean-proof-refinements-2026-10-26.zip::diophantine-lean-proof-refinements-2026-10-26/report/lean-proof-refinements.tex

### RF04: Exact witness before existential erasure

Retain same exact witness in intermediate soundness and derive both existential clients.

Evidence: diophantine-lean-proof-refinements-2026-10-26.zip::diophantine-lean-proof-refinements-2026-10-26/report/lean-proof-refinements.tex

### ST01: Period algebra for helical orbits

Use two-dimensional period lattice for signed helix and seam proofs.

Evidence: proveit-lean-structural-simplifications-2026-10-26.zip::proveit-lean-structural-simplifications-2026-10-26/report.tex

### ST02: Fixed-index-six Pell anchor

Use index monotonicity and exact fixed lower anchor instead of variable-exponent threshold.

Evidence: proveit-lean-structural-simplifications-2026-10-26.zip::proveit-lean-structural-simplifications-2026-10-26/report.tex

### ST03: Signal color moments

Derive actual signal mass from affine color statistics instead of per-index certificate assembly.

Evidence: proveit-lean-structural-simplifications-2026-10-26.zip::proveit-lean-structural-simplifications-2026-10-26/report.tex

### ST04: Canonical operating-row recognition

Retain full receiver tuple and local tile determinism to identify canonical row before south projection.

Evidence: proveit-lean-structural-simplifications-2026-10-26.zip::proveit-lean-structural-simplifications-2026-10-26/report.tex

## Current candidate areas with least direct overlap

The newest controller subset/residue construction and the generic physical-order binding contain recent proof obligations not named in the older reports. This identifies places to inspect, not a novelty guarantee. Exact fixed-kernel quotient identities may be distinct, but generic reflected-parity/carry projection is explicitly rejected as prior in packet o. Existing representation helpers can still contain small arithmetic deletions; preserve their concrete expression, witness counts and executable data.

## Limitations

No global mathematical originality claim is made. Search absence alone is not proof of novelty; decisions above include a comparison to the nearest promised contracts. An unchanged source snapshot appearing in an old packet does not by itself establish an earlier simplification proposal. Conversely, optional notes and uncompiled sketches count as prior. Full old implementation replay is outside this audit.

## Additional candidate: source positivity without marking

The existing selected digit in cell zero proves source positivity for every tile map and arbitrary natural controls; MarkedWord and a marked origin are unnecessary. No exact earlier proposal found. Generic positivity itself is not claimed new.

Decision: Retain exact stronger interface; direct signature migration plus sole Checks call saves 3 physical lines; optional mutually exclusive helper+wrapper adds 10. See `source-selection-report.md` for exact proof, cost, scope, and checks.
