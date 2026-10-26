# Non-repetition audit: DiophantineConsistency Lean proposals

Proof-source snapshot: `4b3dd4efb10f1af27143a6142380322131968726`, inspected 26 October 2026. Final exclusion refresh: `23f631ea07fff8632eb8cd92286f7621bbe051c0`, which adds four incoming proposal archives.

## Scope and method

This audit treats every proposed idea as part of the assumed baseline, including uncompiled sketches, deferred proposals, supplementary source notes, and further-research questions. Adoption status does not make an idea new. A new proof of an old suggestion is useful validation, but does not satisfy this request's novelty constraint.

The initial audit covered all six placed packets a-f under `Computability/DiophantineConsistency/research/lean-proof-simplification/`, its README and ADOPTION record, and all five ZIP archives present in `docs/incoming/` at the proof-source pin. A closing refresh read the four additional manuscripts at the final exclusion pin, bringing the scoped corpus to **fifteen packets: six placed and nine incoming**. The substantive manuscript sections were read, with companion notes, candidate declarations, and patches inspected for omitted or less prominent recommendations. The incoming README was searched throughout for proof-simplification references and its relevant intake summaries read. This is a scoped non-repetition audit, not a claim that no related idea has ever appeared in Lean literature or in every historical manuscript transitively linked from the large intake index.

The exact inventory has 323 placed files, 5 incoming archives containing 400 nondirectory members, and the incoming README. Every placed file and archive member was hashed. Of the incoming members, 251 text/code/patch/metadata members were extracted for local inspection. PDFs and generated objects were hashed as archive members; manuscripts were read from their accompanying TeX. Existing scripts were treated as data, not run. `inventory.json` preserves all paths, byte sizes, hashes and extraction flags. `lean_declaration_index.json` indexes declarations from the supplied Lean artifacts.

The closing delta adds four archives with **1,816 nondirectory members**, of which **1,797 text/code/patch/metadata members** were extracted. The combined incoming inventory is **2,216 members**, with **2,048 extracted text/code members**; many are bundled original source snapshots, not independent recommendations. All four downloaded archive Git blob hashes match the current repository entries. `freshness_delta/inventory.json` records the delta, and `inventory.json` includes both snapshots. The refreshed ADOPTION record contains two additional adoption entries for already excluded mask/carry and residual-sum work; the incoming README is unchanged.

Packets b-f deliberately omit byte-identical source snapshots; five `OMITTED.tsv` manifests document those aliases. They are not missing new proposal text. The manifests have respectively 3, 7, 8, 555 and 945 physical lines (including headings where present); these are not asserted to be counts of unique source files. Existing old-source snapshots and historical compiler receipts are not validation of this review's current candidates.

## Source abbreviations

- **A-F**: placed `2026-10-26a` through `2026-10-26f`, relative to `research/lean-proof-simplification/`.
- **G**: `docs/incoming/diophantine-lean-simplification-2026-10-26(1).zip`, inner directory `diophantine-lean-simplification/`.
- **H**: `docs/incoming/lean-proof-simplification-review-2026-10-26.zip`, inner directory `lean-proof-simplification-review/`.
- **I**: `docs/incoming/diophantine-lean-new-ideas-2026-10-26.zip`, inner directory `diophantine-lean-new-ideas-2026-10-26/`.
- **J**: `docs/incoming/diophantine-lean-new-directions-2026-10-26.zip`, inner directory `new-lean-simplification-2026-10-26/`.
- **K**: `docs/incoming/diophantine-lean-additional-simplifications-2026-10-26.zip`, inner directory `diophantine-lean-additional-simplifications-2026-10-26/`.
- **L**: `docs/incoming/Lean_Proof_Simplification_New_Deltas_2026-10-26.zip`, inner directory `Lean_Proof_Simplification_New_Deltas/`.
- **M**: `docs/incoming/ProveIt_Lean_Simplification_Round2_2026-10-26.zip`, inner directory `LeanReview2/`.
- **N**: `docs/incoming/additional_lean_simplifications_2026-10-26.zip`, inner directory `additional_lean_simplifications_2026-10-26/`.
- **O**: `docs/incoming/diophantine-lean-new-simplifications-2026-10-26.zip`, inner directory `diophantine-lean-new-simplifications-2026-10-26/`.

For A-D, G, I-K, the principal manuscript is `report.tex`; E uses `report/report.tex`, F uses `report/sections/*.tex`, H uses `lean-proof-simplification-review.tex`. References below name exact internal paths and section headings so they remain inspectable without relying on line offsets in the current production files.

For the closing delta, L and O use `report/report.tex`; M uses `report/sections/*.tex`; N uses `report/additional_lean_simplifications.tex`.

## Excluded mechanisms

| ID | Already proposed mechanism | Representative precise evidence |
|---|---|---|
| E01 | Recursor congruence via `simp` or generic `rec_congr`, replacing duplicate induction in PR realizers/optimizer | A report, “Rewrite under primitive recursion”; `lean/RecursorCore.lean`; `patches/pr-congruence.patch` |
| E02 | Core `List.mem_of_getElem?`, `List.getElem?_of_mem`; Option map injectivity | A report “Use the core list-lookup API”; E report section 6 and `checker_examples/standard_library_cleanup.patch` |
| E03 | Assignment naturality under `Sum.map`, evaluator renaming, transport of input/witness blocks | A assignment-map patch; B “Witness layouts”; D “Checked refactor: assignment naturality”; H “A small assignment-transport API” |
| E04 | Existential witness splitting/regrouping using `Fin.addCases`, `Fin.exists_fin_add`, or `Sum.exists_sum` | B `lean/WitnessLayout.lean`; H “Regroup witnesses with the existing sum-type theorem” |
| E05 | Move witness-count/projection/rename lemmas to earlier dependency layers | B “Move existing projection lemmas to their natural home”; C “Share residual-system facts” |
| E06 | Generic validated-history fold with separate input/stored types, append, invariant, Produces composition and certified rule fragments | B “One invariant-preserving history fold”; C `notes/syntax.txt` (ready_binary/ready_unary/fragment2/fragment3); H “An input row and a stored judgment need not have the same type” |
| E07 | Shared Nat.rec iteration, fixed/reject/done states, invariants, and `Function.iterate` bridge | A “Share iteration laws”; B/C/D/E scanner sections; H `lean/ScanIteration.lean` |
| E08 | Shared encoded-list simulation with sufficient fuel, step-cons, distinct rejection/terminal encodings and arbitrary-raw-code soundness | B “Separate recurrence from encoding”; C “Share scanner proofs at the correct semantic boundary”; G “One simulation kernel” |
| E09 | Dynamic-seed/input-dependent PR iterator; supplied program/`.val` preservation | B “A better primitive-recursive iterator interface”; C “Factor the supplied PR iterator” |
| E10 | Exact numeric Boolean output and threshold/tag dispatch normalization on all natural tags | A BooleanCore and “Replace acceptance equivalences”; E section 8 |
| E11 | Shared finite sum-of-squares syntax, evaluation/zero criterion, degree and operation-count bounds | A sections 4/7; B “One executable sum-of-squares API”; C/H compiler sections |
| E12 | Reuse semiring gate soundness/completeness, separate gate data from semantics; combine identical constructor proof branches | B “The semiring theorem already subsumes the natural induction”; E section 5 |
| E13 | Existing `run_power` exponent certificates for generated pure-power chains | A generated-steps; B power certificates; F `report/sections/04_circuits.tex` |
| E14 | Circuit-specific indexed `run_node_equation` facade, selected named wrappers, on-demand proof generation | A/B generated step proposals; F circuit C2 |
| E15 | Generic topological run invariant for uniqueness, nonnegativity, degree/range | A `CircuitInvariant.lean`; C “Use a common DAG invariant theorem”; H “A reusable invariant” |
| E16 | Generic circuit simulation and local NodeRel allowing commuted addition/multiplication | A `NodeRelCommutative.lean`; C “Positive/natural translation is a simulation” |
| E17 | Generic register append topology/dependency/evaluation facts | A `source_notes/circuits-review.md` section 7 |
| E18 | Earlier structural/weighted degree API, weight-one specialization, shared RHS degree bounds | A/C/D degree interfaces; H “Weighted syntax degree” |
| E19 | Cancellation-aware normal-form certificates before degree checking | C “Preserve cancellation-aware degree arguments”; F circuit C4 |
| E20 | Preserve/reuse established register semantic cuts in generators | C “Use established register facts as proof boundaries”; split-register-cuts.patch |
| E21 | Common 99-node Split/Gap tail with boundary-port substitution and insertion theorem | C “Extract the shared 99-node free-carrier tail” |
| E22 | Common scalar FreeCarrierPolynomial ratio tail, map/cast laws, common recipe-tail correctness | E sections 9/11; C shared-tail section |
| E23 | Row-index coefficient-envelope dispatcher; conditional-bound tactic; common nonnegative monomial context | C “Compress the coefficient-row proofs”; D “Coefficient envelopes”; G narrow envelope tactic |
| E24 | Finite signed-monomial majorant certificates retaining sharp dependence on K | C “A stronger abstraction: a finite majorant certificate”; D further research |
| E25 | Coefficient expression syntax / single AST, generic naturality by homomorphism interpretation | C “Do the same for coefficient naturality”; F architecture A6 |
| E26 | Sparse quadratic row normalization tied to independently supplied residual/source data | C “A small sparse-row normalizer”; G low-degree row certificates |
| E27 | Elementary row additions and surjective row reindexing preserve common zero sets | C “Represent elementary row operations once”, `lean/checked/RowOperations.lean` |
| E28 | Exact scaled half-radix quotient/remainder identity instead of finite case enumeration | A/B/C/D/G half-radix sections |
| E29 | Weaken modulo 2048 reflected coefficient to modulo 16 using divisibility | A modulus-reuse.patch; B/C/G congruence sections |
| E30 | Conditional padding witness eliminates irrelevant dummy witnesses | A conditional-padding.patch; A digits-review section 1 |
| E31 | Exact digit/carry decomposition gives quotient, remainder, modular projection, zero carry | A NormalizationArithmetic; B CarryCertificate; E equation-side carry lemmas |
| E32 | Derive rather than store redundant `Facts.carry_recurrence`; small named carry/window views | A digits-review section 3; C “Improve the current-window API”; D carry records |
| E33 | Shared ambient cyclic modulus/field residue/offset/nonorigin support facts | A digits-review section 5; B physical-field residues; D generic cyclic residues; G cyclic-field interface |
| E34 | Aligned-cell equivalence with `ZMod N`, reindexing and reuse existing Cell type | B report lines 613-615; E section 12; J `evidence/prior_ideas.md` E29 explicitly warns that a basic AddEquiv is too close |
| E35 | No-borrow origin decrement word law, separate low +1/high -1 corrections | A digits-review section 6; G “One origin-correction lemma” |
| E36 | Direct physical selector sum API avoids prefix-sum round trips | A digits-review section 7 |
| E37 | Coherent restored source/window extraction preserves the same source and N across low/high/full window | A digits-review section 8; F architecture A3 |
| E38 | Decode common source/Pell register equations once; semantic identities and Nat/Int rank conversion | B “Decode source-register equations once”; C `notes/arithmetic.txt` section 6 |
| E39 | Generic finite table chunk/tail dispatcher, balanced block assembly, finite sum chunks | B “Keep checked finite chunks”; E section 13; WangTiles942Data and CurrentKernel2011 are explicit targets |
| E40 | Shared copied-field bounds, finite direction/offset/width descriptor and 34-control reindexing | B “One copied-field bound interface”; E section 13 |
| E41 | Optional mask-block lookup/length/bound API | E section 13, “Optional mask-block reuse” |
| E42 | Definable induction transport with explicit object formula and satisfaction witness | A “A definable-induction transport lemma”; G “Wrap internal induction” |
| E43 | Shared model-axiom extraction/completeness/sealing bridge retaining arbitrary models and contexts | A/B/C/D/E/H object endpoint sections |
| E44 | Arity-polymorphic closed-sentence/environment transport | B “Generalize closed-sentence transport”; C “An especially small arity-polymorphism improvement” |
| E45 | Generic finite-index row-family facts for internal naturals (`Fin.forall_fin_add`, `forall_fin_two`), quantified List.ofFn simplification | C “Build on algebraic interfaces already present”; G object finite-index section; H `inputsNaturalForm_spec` |
| E46 | Nine-coordinate packaging equivalence with coordinate 7 left unshifted | F architecture A1; `NineCoordinatePackaging.lean` |
| E47 | Parameterized sharp Split/Gap numerical degree profiles and leading-coefficient bounds | F architecture A2 |
| E48 | Lower CurrentCarrierBase import layer/facade avoiding thirteen-coordinate completeness dependencies | F architecture A4 |
| E49 | Named conjunction accessors and derived positivity projections | F architecture A5 |
| E50 | Local standard-algebra reductions: Carrier66 positivity/canonical zero; `run_map`; whole-disjunction cast in FirstPellCarrier | E sections 3-5, exact algebra patches |
| E51 | Specialize existing half_base_bound at 31; Finset intersection for mask sums; predecessor power identity; convolution distributivity; `Nat.one_lt_two_pow`; finite-switch boundary | F `report/sections/02_local.tex` and tactics candidates |
| E52 | Finite-fiber/pushforward identity for foldStencil mass, convolution and word | D “One finite-fiber identity for folded stencils”; FinitePushforward prototype |
| E53 | Injective sparse placement API distinct from general colliding foldStencil; Fin-to-ZMod transport | G “Separate arbitrary folding from injective sparse placement”; H finite-word boundary |
| E54 | Guarded solvability congruence/transport and composition, without unnecessary witness bijections | E section 10 and SolutionTransport.lean; G positiveZero_congr |
| E55 | Shared direct/native graph enumerator builder with separate cost projections | E section 14; exact rawStepProgram/boundedRunProgram duplicates |
| E56 | Parser-then-check composition, generic quotation injectivity via partial decoder | G “Reuse parser and list infrastructure”; checker source notes |
| E57 | Successful Option.bind inversion to remove impossible decoder branches; combined decoder graph/fuel theorem | H decoder-options (with axiom distinction); J/K exact decoder graph sections |
| E58 | Pell parity theorem reuse in NativePellStepDown | I “Reuse the already proved Pell parity criterion” |
| E59 | Signed congruence up to ±1 as transitive relation; absolute value transport; half-interval equality | I sign section; J signed congruence section and algebra_review.md |
| E60 | Product-equivalence inverse projection graph theorem, including pairing/Cantor extension | I “Derive inverse graphs from a product equivalence” and further questions |
| E61 | Shared positive-denominator Euclidean certificate and full quotient/remainder/slack uniqueness/coherence | E section 6; I Euclidean certificate section and further questions |
| E62 | Affine composition-depth/witness budget helper and removal of ordinary graph nonempty-arity premise | I “Factor the arithmetic budget”; further questions |
| E63 | Certified max-plus/depth-budget summaries, local constructor adapters and expression traversal preserving let sharing | I further question; J “Synthesize representation-depth bounds” |
| E64 | Internal tagged constructor/no-confusion views and combined unique-existence code induction | J “Constructor views and one internal unique-existence induction” |
| E65 | Internal recursive-graph invariant/preservation/fusion, retaining exact definable predicate | J “Preservation and fusion for internal recursive graphs” |
| E66 | Explicit least/greatest cyclic carry formulas, two-solution classification and budget selection | J “An optional structural alternative: explicit cyclic carries”; algebra_review.md |
| E67 | Preserve chosen rational witnesses on integer descent using denominator-one integrality | K “Preserve rational roots when descending to integers” |
| E68 | Decompose product units once using IsUnit.mul_iff/Int.isUnit_iff | K “Decompose the product's units once”; E has older factor-by-factor unit simplifications |
| E69 | Finite invariant reflection/restricted injection surjectivity instead of periodic predecessor orbit | K “Use finiteness to recover an invariant predecessor” |
| E70 | Polynomial support envelope first, then coefficient vanishing via natDegree | K “Prove the support envelope before individual coefficients” |
| E71 | Rotation as convolution with a point mass, reuse word_convolution | K “Rotation is convolution with a point mass” |
| E72 | Scoped fun_prop registrations for extensional Primrec composition, separate from supplied program syntax | K “Automate extensional primitive-recursiveness composition” |
| E73 | Fixed raw+digit carry uniqueness via finite maximum principle; fixed-length packing injectivity | K “Canonical normalization from a finite maximum principle” |
| E74 | Support-restricted evaluator congruence/frame rules, signed Expr extension of existing WitnessCompaction.eval_congr | J `evidence/prior_ideas.md`, candidate 7, including subsequent maintained-source caveat |
| E75 | Normalize schema renaming chains by algebra of index maps | J `evidence/prior_ideas.md`, candidate 8; `evidence/semantic_review.md` section 5 |
| E76 | Cyclic packing via monoid algebra/quotient-ring homomorphism | J `evidence/prior_ideas.md`, candidate 9; `evidence/algebra_review.md` optional direction |
| E77 | General profiling, simp boundaries, small checked certificates, sharding, generator/output synchronization, compatibility wrappers, explicit audit policies/import coverage | All manuscripts; F validation and import census. These are sound practices, not new proposal mechanisms. |
| E78 | Future finite-state controller invariants only after actual decoder binding; SCC/ranking for cycle exclusion | E report section 13, final paragraph. This does not specifically propose Wang step/tape decomposition, but generic finite-state-invariant language is already present. |

| E79 | Replace artificial trivial existential lets by `set ... with ...` in NativeHalfBinomial.upper_estimate_scaled | H `evidence/arithmetic/findings.txt`, section 8, “Minor readability improvements in analytic estimates” |
| E80 | Standard natural subtraction/remainder identities; let omega handle supported Nat/Int casts; keep huge powers symbolic | H manuscript “Natural subtraction and remainder”, “Let omega handle the cast interface”, “Keep huge powers symbolic”; `evidence/arithmetic/findings.txt` sections 4-6 |
| E81 | Shared semantic binaryForm/unaryForm constructors and code/rename/bound laws remove repeated valid-tag branches | H `evidence/syntax/findings.txt` section 6; applies to AnnotatedRename.binary_sound and AnnotatedBound.binary_sound |
| E82 | Central `zero_pair : Nat.pair 0 n = n*n` and reuse generic syntaxDegree_rename | H `evidence/syntax/findings.txt` section 7 |
| E83 | Dedicated natural-semiring evaluator with erasure correctness, preserving typed register costs | H `evidence/structural/findings.txt` section 7; manuscript final paragraph before validation |
| E84 | Directly specialize binaryWord_prefix at South offsets 19/20, normalizing addresses under lambdas | L `report/report.tex`, page heading 4; M `report/sections/06_south_prefix.tex` |
| E85 | Reuse theta of an aligned representative as the exact difference-cell reachability witness | L `report/report.tex`, page heading 5, `CurrentCellCycle2011.reachable_from` |
| E86 | Make zero-base cell propagation a specialization of existing propagate_from, with declaration reorder | L page heading 5; M `report/sections/05_finite_and_cycle.tex`, C4 |
| E87 | Guarded symbolic North/South tile-color fibers, or color-indexed NorthView, to share exact boundary classification | L page headings 6–7; M `report/sections/08_north_view.tex` |
| E88 | Characterize alternate marked assignments by their selected bits in the same original word, then transport existing marked-word correctness | L page heading 8, `assignment_eq_iff_selector` and `facts_marked_word_of_selector` |
| E89 | Replace raw parent-code reconstruction by existing total table decoding, exact re-encoding and check_lists | M `report/sections/03_parents.tex`; `annotated/REVIEW_NOTES.md`, A |
| E90 | Hoist existing binaryWord_congr to the definition layer and reuse it in copy-word and horizontal-word clients | M `report/sections/07_word_congruence.tex`; `current/current_findings.txt`, C3 |
| E91 | Replace CRT modulus tactic search by explicit congruence transport through add/multiply/add | M `report/sections/09_supplemental.tex`, S1; `supplemental/crt-explicit-congruence.patch` |
| E92 | Uniform Pell fundamental-unit criterion for positive ordinate at most three, replacing firstUnit_fundamental entirely | N `report/additional_lean_simplifications.tex`, lines 283–370; `patches/main.patch` |
| E93 | Consume quadratic Boolean zero-certificate equivalence before assembling conditional witnesses | N report section “Consume the Boolean certificate before constructing a conditional” |
| E94 | Package physical-position injectivity as Fin.cons of zero and a positive injective strict-rank tail | N report section “Optional: recognize the physical permutation as a positive tail”; `optional/permutation-injectivity.patch` |
| E95 | Replace internal omega_ind proofs whose induction hypothesis is unused by existing nat_zero_or_succ decomposition | O report Idea 1, ObjectAdditionCancellation.addRel_zero_iff and ObjectNaturalZero.mulRel_zero_iff; further audit question |
| E96 | Prove simultaneous Pell-coordinate monotonicity in the base, compare indices directly, and inspect weaker base-separation obligations downstream | O report Idea 4 and further research questions; NativePellBootstrap.main_index_gt_first |
| E97 | Keep nonsquare integer norm proof integral via Int.pow_dvd_pow_iff and cancellation of a nonzero square | O report Idea 5, MinimumNorm.norm_ne_zero_of_not_isSquare |
| E98 | Share the general separated-norm integer-root theorem below both finalizer clients, retaining signed nonzero weights | N report “Put the general separated theorem below both clients”; overlaps E67's exact-root descent but adds this explicit theorem-placement/generalization obligation |

Other closing-delta suggestions were already covered: M's joint decoder invariants by E57 and binary composition-depth helper by E62; N's exact rational descent by E67, Pell parity by E58, signed congruence by E59, and inverse pairing projections by E60; O's parity, additive signed-divisibility transport, and finite inverse-invariance argument by E58/E59/E69. They remain excluded regardless of different local implementations.

## Overlap judgments for the current research pass

The following candidate mechanisms were checked against both manuscript prose and artifacts. Absence claims concern this corpus and snapshot.

| Candidate | Judgment | Boundary |
|---|---|---|
| Integer induction centered at arbitrary x0, or translated zero induction, for WangTiles942ResetRows.interval_propagate | Not found; strong new local candidate | Different from Nat.rec scanner laws; replaces two one-sided inductions plus toNat transport in an integer interval proof. The delivered complete module uses the choice-free translated variant. |
| Bounded first-failure/prefix certificate for WangTiles942InitialStrip left/right wall existence | Not found; new candidate | Must retain differing left/right edge colors and geometry. Generic scanner iteration alone does not supply least-failure minimality. |
| Intrinsic shared-edge Wang step row, with one bridge signal and north/south colors supplied by the operating configuration | Not found; new candidate | Horizontal matching follows from a single edge field; this changes the proof representation, rather than introducing previously proposed finite-state controller certificates. Actual finite-language membership and equality with the maintained step row remain separate obligations. |
| Monotone finite-certificate closure under empty/union/insertion for ObjectCodeBound | Not found as an explicit proposal | Existing J constructor views/unique existence and recursive-graph preservation are baseline; candidate must prove the separate certificate assembly law, not rephrase those ideas. |
| Cell kernel/AddEquiv/group-action transport alone | High overlap; exclude as a standalone novelty claim | E34 already proposes aligned-cell equivalence, and J explicitly says a basic AddEquiv is too close. An entirely new downstream theorem would need a separate case. |
| Generic `Exists.congr` normalization alone | Overlap | E04/E54 already lift pointwise equivalences through guarded existential packaging. |
| Generalize NativeHalfBinomial/PellRatio90 upper estimates to a common scale-dependent error | Not found; new candidate | H's E79 only suggests replacing trivial existential lets by `set`; it does not share or generalize the analytic inequality. |
| One stronger rank envelope (2q−1)(q²−1) ≤ nativeRank, then derive 40 ≤ nativeRank and 3q < nativeRank while retaining the existing 24-bound wrapper | Not found as this stronger mathematical argument | E38 already proposes a source-facts API carrying known lower bounds; novelty lies in deriving q−F≥2 from the positive transport gap and hence the factor 2q−1, and sharing the nonlinear derivation. A new record alone is baseline. |
| NativePellBootstrap.firstUnit_fundamental via a sign-free lattice-square certificate | **Withdrawn after closing refresh** | N/E92 replaces this entire proof with a generic small-ordinate criterion. Once that earlier proposal is assumed applied, the competing-square proof to be shortened is gone. A different elementary mechanism is insufficient to retain it as a new recommendation. |


## Current-source context

The ADOPTION record explicitly marks many low-level proposals adopted, pending or deferred; all are excluded equally here. It also records that TotalDegreeBound already independently replaced degree certificates in ShortSystem, ShortFrontier and ShortReducedStrong. Thus introducing a degree-bound tactic is not a new suggestion for this pass.

The incoming README retains historic K215 simplification summaries (shared recursion/quotient syntax, implication successors, semantic import cuts, certificate-based proof assembly). Their generic ideas are not claimed as novel here. The audit did not recursively open every retired archive linked outside the two user-specified current directories; that much larger literature claim is neither needed nor asserted.

## Archive digests

| Incoming archive | Nondirectory members | SHA-256 |
|---|---:|---|
| diophantine-lean-additional-simplifications-2026-10-26.zip | 84 | `8c849deed06484fe7da0513703ad0eb95332e77f12645451a1bd12e373a82be9` |
| diophantine-lean-new-directions-2026-10-26.zip | 39 | `9d31a37f69f3a29042e480542c3073a8eb1f65d1e0e0ebd2dba7c820eee9c5d0` |
| diophantine-lean-new-ideas-2026-10-26.zip | 80 | `0941e8297fefe672af5d029878e07d392b502b0aa2bd67e8a8ace0d2aba2ff70` |
| diophantine-lean-simplification-2026-10-26(1).zip | 73 | `c8d7d56a0344f141dc7d2e44c63b0ee450d552205d4ae9c8d10076cd310e1118` |
| lean-proof-simplification-review-2026-10-26.zip | 124 | `9d9eb709f2d454c4439d2e1f822dbe1b1bcda3cb0f3eedcf5338542b1fbe1ecb` |
| Lean_Proof_Simplification_New_Deltas_2026-10-26.zip | 669 | `cf8ae50a36fef2600d87867818f8f562eab42f3b1c9187f41580e94e77f8ce5f` |
| ProveIt_Lean_Simplification_Round2_2026-10-26.zip | 945 | `4fb50b527a8cead896aaa8e5d3328eec7cdc2b5cc6c85a3388b44ea88528c543` |
| additional_lean_simplifications_2026-10-26.zip | 140 | `f35810a3e2f1a74ea13e52596ec8965cd3eabb040de9aa451243d2e0dd92fc9e` |
| diophantine-lean-new-simplifications-2026-10-26.zip | 62 | `3f65634b03124ed8353651baadd63e4cb7ae5664755ec5b43c8052fd82fce09d` |

No archived prior-proposal compiler receipt was replayed by this audit. New-candidate correctness was reviewed separately in `reviewer_notes.md`, using the latest current receipts.

## Current candidate validation update

`semantic_work/full-module-validation.json` records ten successful Wang checks: two complete modified modules, six unchanged supporting modules, and two unchanged original Checks clients. The actual `WangTiles942ResetRows.interval_propagate` candidate uses translated zero induction and retains `[propext, Quot.sound]`; the shorter centered `Int.inductionOn'` variant is optional and adds `Classical.choice`. The generic shared-edge row remains a separately checked design kernel whose production equality and Allowed-membership binding have not been implemented.

`root_work/rank-metrics.json` records a final combined rank-module size of 769 to 765 physical lines. `root_work/final-checks.json` records successful final ScaleBounds, rank-axiom, and trace-axiom checks. The four-line raw reduction includes natural/integer cast cleanup, a mechanism already within E38's scope; novelty is assigned to the stronger `(2q-1)(q²-1)` mathematical envelope, not to repackaging old rank or cast facts.

The closing exclusion refresh removes the previously checked sign-free Pell fundamental-unit candidate from the retained recommendations. Checking it remains valid historical evidence, but it must not be counted as new work after E92 is assumed applied. The other five main candidate mechanisms and the small trace rewrite were not found in the four additional manuscripts, their proposal notes or patches.
