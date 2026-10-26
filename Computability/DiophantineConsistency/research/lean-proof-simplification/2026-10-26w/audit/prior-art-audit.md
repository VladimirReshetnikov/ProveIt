# Prior-proposal exclusion audit

Reviewed snapshot: `553a5f7a463cbaab8800ff8148fef0bc5a9e1b22`, 26 October 2026 (user time zone).

## Scope and interpretation

This audit covers six placed packets, 2026-10-26a through 2026-10-26f, and all twelve ZIP archives physically present in `docs/incoming` at the snapshot. The ZIPs were treated as inert data; no supplied program was executed. Reports, delivery notes, substantive source/review notes, exclusion ledgers, and proposed interfaces were inspected or searched. The member inventory records all 2,405 non-directory ZIP entries, with byte sizes and SHA-256 hashes. Reading a member or hashing it is not a Lean validation claim.

All previous ideas count as applied, including optional, deferred, uncompiled and unselected proposals. A newly compiled old mechanism is new validation, not a new idea. The `ADOPTION.md` distinctions therefore do not narrow the exclusion set. In particular, existing finite-residual helpers and TotalDegreeBound already appear in the adoption record.

The very long incoming README also indexes historical work outside the two requested locations. This audit uses that index for routing; it does not claim to re-review every unrelated manuscript transitively linked there. Novelty claims should say “not found in the eighteen directly audited proof-simplification packets,” rather than claim global priority.

## Exact corpus key

Let `P` denote `Computability/DiophantineConsistency/research/lean-proof-simplification`.

| Key | Exact report location | Additional notes inspected |
|---|---|---|
| A | `P/2026-10-26a/report.tex` | `source_notes/{checker,circuits,digits}-review.md`, proposal and checked-module inventory |
| B | `P/2026-10-26b/report.tex` | native/compiler reviews and proposed interfaces |
| C | `P/2026-10-26c/report.tex` | `notes/{syntax,arithmetic,circuits}.txt` |
| D | `P/2026-10-26d/report.tex` | interface review, finite pushforward and rotation files |
| E | `P/2026-10-26e/report/report.tex` | native prototypes and architecture inventory |
| F | `P/2026-10-26f/report/sections/*.tex` | architecture findings, tactics and circuit review |

### I01 — `docs/incoming/Lean_Proof_Simplification_New_Deltas_2026-10-26.zip`

SHA-256: `cf8ae50a36fef2600d87867818f8f562eab42f3b1c9187f41580e94e77f8ce5f`. Non-directory members: 669.

Main report members: `Lean_Proof_Simplification_New_Deltas/report/report.tex`.

### I02 — `docs/incoming/ProveIt_Lean_Simplification_Round2_2026-10-26.zip`

SHA-256: `4fb50b527a8cead896aaa8e5d3328eec7cdc2b5cc6c85a3388b44ea88528c543`. Non-directory members: 945.

Main report members: `LeanReview2/report/preamble.tex`; `LeanReview2/report/sections/01_recent_commits.tex`; `LeanReview2/report/sections/02_novelty.tex`; `LeanReview2/report/sections/03_parents.tex`; `LeanReview2/report/sections/04_decoder.tex`; `LeanReview2/report/sections/05_finite_and_cycle.tex`; `LeanReview2/report/sections/06_south_prefix.tex`; `LeanReview2/report/sections/07_word_congruence.tex`; `LeanReview2/report/sections/08_north_view.tex`; `LeanReview2/report/sections/09_supplemental.tex`; `LeanReview2/report/sections/10_metrics_validation.tex`; `LeanReview2/report/sections/11_corpus_artifacts.tex`.

### I03 — `docs/incoming/additional_lean_simplifications_2026-10-26.zip`

SHA-256: `f35810a3e2f1a74ea13e52596ec8965cd3eabb040de9aa451243d2e0dd92fc9e`. Non-directory members: 140.

Main report members: `additional_lean_simplifications_2026-10-26/report/additional_lean_simplifications.tex`.

### I04 — `docs/incoming/diophantine-lean-additional-simplifications-2026-10-26.zip`

SHA-256: `8c849deed06484fe7da0513703ad0eb95332e77f12645451a1bd12e373a82be9`. Non-directory members: 84.

Main report members: `diophantine-lean-additional-simplifications-2026-10-26/report.tex`.

### I05 — `docs/incoming/diophantine-lean-new-directions-2026-10-26.zip`

SHA-256: `9d31a37f69f3a29042e480542c3073a8eb1f65d1e0e0ebd2dba7c820eee9c5d0`. Non-directory members: 39.

Main report members: `new-lean-simplification-2026-10-26/report.tex`.

### I06 — `docs/incoming/diophantine-lean-new-ideas-2026-10-26.zip`

SHA-256: `0941e8297fefe672af5d029878e07d392b502b0aa2bd67e8a8ace0d2aba2ff70`. Non-directory members: 80.

Main report members: `diophantine-lean-new-ideas-2026-10-26/report.tex`.

### I07 — `docs/incoming/diophantine-lean-new-simplifications-2026-10-26.zip`

SHA-256: `3f65634b03124ed8353651baadd63e4cb7ae5664755ec5b43c8052fd82fce09d`. Non-directory members: 62.

Main report members: `diophantine-lean-new-simplifications-2026-10-26/report/report.tex`.

### I08 — `docs/incoming/diophantine-lean-post-roadmap-2026-10-26.zip`

SHA-256: `5a60c17dda4f7114745159a1de8a198574cd834b01461d665c2cba9d6904fe4d`. Non-directory members: 90.

Main report members: `diophantine-lean-post-roadmap-2026-10-26/report/new-proof-simplifications.tex`.

### I09 — `docs/incoming/diophantine-lean-simplification-2026-10-26(1).zip`

SHA-256: `c8d7d56a0344f141dc7d2e44c63b0ee450d552205d4ae9c8d10076cd310e1118`. Non-directory members: 73.

Main report members: `diophantine-lean-simplification/report.tex`; `diophantine-lean-simplification/validation-summary.tex`.

### I10 — `docs/incoming/lean-proof-simplification-new-2026-10-26.zip`

SHA-256: `d003ea6a17092131f64fff4d05e209136a486072e45d5d4dd726b446d4e364a1`. Non-directory members: 69.

Main report members: `lean-proof-simplification-new-2026-10-26/report.tex`.

### I11 — `docs/incoming/lean-proof-simplification-review-2026-10-26.zip`

SHA-256: `9d9eb709f2d454c4439d2e1f822dbe1b1bcda3cb0f3eedcf5338542b1fbe1ecb`. Non-directory members: 124.

Main report members: `lean-proof-simplification-review/lean-proof-simplification-review.tex`.

### I12 — `docs/incoming/lean-simplification-residual-2026-10-26.zip`

SHA-256: `640f1e9fb1e4dbbffb99bd8563aee161bf710e4b517cdde5027b7154fe6dd579`. Non-directory members: 30.

Main report members: `lean-simplification-residual-2026-10-26/report.tex`.

## Excluded structural, syntax and compiler mechanisms

| Mechanism already proposed | Exact nearest sources |
|---|---|
| Core list getElem?/membership and Option map injectivity instead of bespoke induction. | A; E; F; I11 “Seven list inductions”. |
| Generic congruence under Nat.rec; optimizer proof by recursor congruence. | A “Rewrite under primitive recursion”, `lean/RecursorCore.lean`. |
| Assignment naturality, Sum.map renaming, finite witness splitting/regrouping, early placement of constructor projections. | A–D; I09 assignment transport; I11 assignment API. |
| Shared iterate/fixed-state/successor/zero scanner laws, raw-code soundness, encoded-list simulation, supplied iterateFrom programs. | A–E; I09 common scanner kernel; I11 validated history. |
| Validated history folds, Produces append/step and certified fragments. | B history fold; C `notes/syntax.txt` explicitly ready_binary/ready_unary/fragment2/fragment3. |
| Exact Boolean numeric values, finite tag dispatch, consuming a Boolean certificate before a conditional. | A/B numeric Boolean sections; I03 “Consume the Boolean certificate…”. |
| Shared residual SOS evaluation, zero criterion, degree and operation counts. | A–F; I11 finite residuals; already recorded adopted in ADOPTION. |
| Generic semiring gate correctness / natural compiler specialization after syntax-layer extraction. | B/D compiler sections; E gates examples. |
| Generic topological DAG invariant for uniqueness, nonnegativity, degree/range. | A/C; I11 reusable invariant. |
| Reuse run_power and exponent labels; generated local gate specialization; indexed/lazy facade; shared generator templates. | A/B/F generated-circuit sections. |
| Existing register cuts; shared 99-node free-carrier tail; semantic block certificates bound to exact parent embedding. | C tail/cuts; E section 9/11; F semantic blocks. |
| Generic positive/natural circuit simulation and commuted add/mul NodeRel; append/frame index invariants. | A/C translation sections; A NaturalRegisterProgram append proposal. |
| Shared weighted/structural degree helpers, prefix/profile certificates, cancellation-aware rewriting, total_degree_bound. | A–F; ADOPTION records TotalDegreeBound already independently applied. |
| Checked/typed circuit view, SafeNode with Fin earlier operands, erase-to-literal-list certificate. | F “Treat typed circuit views…”. |
| Nine-coordinate packaging preserving slot 7; long-conjunction accessors; coherent source/window record. | F architecture sections; E solution transport. |
| Parameterized direct/native graph enumerator control-flow builder preserving 6,924/1,742 witness counts. | E section 14 “Share control flow without collapsing cost models”. Extending the same frontend idea to Scalar backend is not a distinct headline mechanism. |
| Decoder Option simplification; fused quotation/depth induction; exact graph `decode fuel code = some t ↔ quote t = code ∧ depth t ≤ fuel`. | I11; I04 exact graph; I05 decoder graph. |
| Total decoding bridge for arbitrary parent codes. | I02 A1 and `annotated/REVIEW_NOTES.md`. |
| Pairing inverse coordinate graphs by existential projection/product equivalence; exact data preservation. | I03 pairing; I06 inverse graphs. |
| Canonical quadratic-pairing selector, slack and maximum witnesses. | I10 E; this is stronger than old output-only pairing soundness and itself already proposed. |
| Successor-first fork certificate preserving every witness, then isolate zero/predecessor boundary. | I10 C. |
| Variadic arbitrary-premise backward-index fragment collection/finishing once. | I10 B, in addition to older fragment composition notes. |
| Affine composition cost/depth budget; max-plus/two-number representation-depth certificate synthesis. | I06 budget; I05 depth; I02 S2 binary bookkeeping. |
| Single structural rule-schedule syntax compiled to numeric and supplied-PR backends; all 17 tags plus invalid default; preserve supplied tree/counts. | I12 section 5, `evidence/structural_ideas.md`. |
| Extensional Primrec closure automation with scoped fun_prop rules. | I04 section “Automate extensional primitive-recursiveness composition” and `notes/checker.md`. |
| Support-restricted evaluator congruence and overwrite/frame rules. | I05 `evidence/prior_ideas.md` candidate 7; existing WitnessCompaction.eval_congr. |
| Certified normalization of AnnotatedSchemaMaps rsep/rf1/rf2/ri renaming-map chains. | I05 `evidence/prior_ideas.md` candidate 8; `evidence/semantic_review.md` section 5. |

## Excluded arithmetic, native words and finite certificates

| Mechanism already proposed | Exact nearest sources |
|---|---|
| Half-radix scaled div/mod identity; quotient, parity and bound consequences. | A–D arithmetic sections. |
| Strong congruence projects to weaker moduli by divisibility. | A modulus-reuse; C/D current-window sections. |
| Conditional padding witness rather than dummy outer witnesses. | A conditional-padding patch. |
| Exact digit/carry decomposition; derive recurrence/remainders/reset/modular projection; named carry record. | A–E; I09 recurrence derivation. |
| Aligned Cell ≃ ZMod N; modular field residues; wrapped temporal translations; off-origin geometry. | A digits-review section 5; B physical-field residues; D cyclic residues. |
| No-borrow origin decrement and common mask-origin correction. | A digits-review section 6; I09 origin-correction section. |
| Direct physical selector-sum identity avoids prefix-sum roundtrips. | A digits-review section 7. |
| Coherent canonical source/window extraction, WordFacts views. | A digits-review section 8; E/F architecture. |
| Finite-fiber weighted pushforward allowing collisions; separate injective sparse placement; bounded positions through Fin/ZMod. | D FinitePushforward; I09 folding/sparse-placement section. |
| Coefficient-row envelope schema; finite dispatcher; monomial majorant certificate; coefficient naturality; sparse quadratic normalizer. | C/D; I11 coefficient certificate. |
| Elementary row addition / surjective reindexing preserves simultaneous zero sets. | C RowOperations. |
| Decode source/Pell row equations once and share Nat/Int conversion. | B “Decode source-register equations once”. |
| Generic finite chunk assembly/dispatch; copied-field descriptors/bounds. | B native certificate section; E native prototypes. |
| Guarded solution transport / zero-set equivalence respecting domains. | E section 10; I09 zero-set congruence. |
| Positive-denominator quotient/remainder/slack certificate shared across graph backends, including canonical uniqueness. | E section 6; I06 DivMod certificate. |
| One-hot finite support classification using sum_le_one_iff. | I06; I09; I11; I02 C1. |
| Existing Pell odd-index criterion; removing redundant Nat/Int residue cast witnesses. | I03/I06 parity; I11 casts. |
| Signed congruence as transitive ± relation/orbit; natAbs invariance; keep divisibility witnesses abstract. | I03/I05/I06 sign relation; I07 idea 3. |
| Exact rational-root integral descent retaining the roots and all witness signs. | I03/I04. |
| Decompose product units in one theorem. | I04 product-unit section; E narrower units examples. |
| Uniform small-ordinate criterion for Pell fundamental/minimal solution. | I03. |
| Pell comparison through simultaneous base monotonicity; strict-index gap via base+index monotonicity. | I07 idea 4; I12 first proposal. |
| Pell ratio estimate with variable positive error factor; common natural perturbation/majorant kernel and tolerance budget. | I10 A; I12 second proposal. |
| Half-binomial extraction through exact natural quotient, avoiding the real fractional witness. | I12 third proposal, using existing binomial_floor_two. |
| Integer-only norm proof; negative Pell obstruction derived from positive units; normalize four residue obstructions to one existing theorem. | I07 idea 5; I08 sections 3–4 and `minima/new_directions_audit.md`. |
| Heterogeneous nonzero minima saturation using Finset.sum_eq_sum_iff_of_le and block equality cases. | I08 section 5, `minima/new_directions_audit.md`. |
| Finite invariant subset is closed under inverse/permutation; avoid explicit periodic-orbit bookkeeping. | I04 `notes/finite-invariant.md`; I07 idea 6. |
| Polynomial support envelope first, coefficients second. | I04 support-envelope section. |
| Rotation as convolution with a point mass. | I04 point-mass section. |
| Support-displacement exclusion projected through a quotient homomorphism. | I10 D, concrete 606∉S−S native client. |
| Fixed-length digit injectivity via Nat.ofDigits_inj_of_len_eq; full-word normalization coherence; finite maximum principle gives unique carry for fixed digits. | I04 report lines 348–394; I10 novelty ledger explicitly classifies these as prior. |
| Closed-form least/greatest cyclic carries from rotated weighted sums; exact two-solution ambiguity and budget selects least. | I05 explicit-carry section, `evidence/algebra_review.md`. |
| Cyclic packing as additive-monoid-algebra homomorphism into ZMod(radix^n−1); derive convolution/rotation. | I05 `evidence/prior_ideas.md` candidate 9 and optional section of `evidence/algebra_review.md`. |
| Direct South binaryWord_prefix specialization for offsets 19/20. | I01 proposal 1; I02 C2. |
| Hoist binaryWord_congr and reuse in copied words/horizontal words. | I02 C3. |
| Use theta as exact difference-cell witness; zero-base propagation as arbitrary-base specialization. | I01 proposal 2; I02 C4. |
| Guarded north/south equality-indexed color fibers; static exact-color corollaries specialize them. | I01 proposals 3; I02 W1. |
| Alternate selector assignment equals existing assignment by same original-word selected-bit equations; transport marked-word proof by equality. | I01 optional proposal 4. |
| Physical permutation recognized as a positive tail. | I03 optional proposal. |
| Named existing CRT congruence. | I02 S1. |

## Excluded object-model mechanisms and methodology

- Actual-formula definable induction transport over arbitrary internal naturals: A/C/E.
- Shared model-to-ZF-axioms, validity/completeness/sealing boundary and arity-polymorphic closed-sentence transport: A–D and I11.
- Model-independent finite-index/row-family algebra shared with internal-natural arithmetic while retaining definability: C notes; I09.
- Constructor views/inversion and one definable unique-existence code induction: I05.
- Internal ThetaG recursive-graph preservation/fusion with stage-formula witnesses: I05.
- Delete vacuous arithmetic inductions whose induction hypotheses are unused (two concrete addition/multiplication clients): I07/I08.
- Monotone local-certificate calculus for derivation closure: I08 optional section.
- Profiling, smaller simp sets, shared generator templates, source-vs-kernel measurements, axiom gates, audit manifests, certificate sharding and compatibility wrappers are established methodology, not new ideas.

## Specific novelty decisions for the present round

### Cleared: certified trace rows and boundary-to-boundary composition

The current proposed target is repeated state splits in `WangTiles942TraceCycle` run-tile allowedness/north/south/horizontal facts and repeated index splits when gluing the trace cycle. No prior packet proposes a certified run-row object with exact boundary color functions, horizontal matching and composition of rows/stages. The closest earlier idea is I01/I02 static color-fiber classification of individual allowed tiles. The report must explain that the new reusable invariant describes an entire run row and composes trace stages; simply renaming a tile color classifier would repeat old work.

### Cleared: remove helical shifts by an explicit shear of integer coordinates

No prior substantive text proposes `(x,t) ↦ (x+w*t,t)` to conjugate a helical lattice period into an ordinary vertical period, nor its use to replace the integer induction in `WangTiles942HelicalExtension`. Old aligned-cell equivalences and packing homomorphisms are one-dimensional arithmetic encodings, not this two-dimensional change of coordinates. I01 says its then-existing periodic-plane wrappers were already short; the present proposal therefore needs concrete newly added clients and an honest helper-inclusive payoff.

### Cleared: twisted-band quotient equivalence and equivariant descent

No prior proposal constructs the quotient/remainder bijection between a twisted fundamental band and `ZMod (w*H)` and proves matching/marker uniqueness by a shared equivariant-surjection theorem. This is distinct from old `Cell ≃ ZMod N` and support projection; preserve negative coordinates, period orientation and marker uniqueness hypotheses. A new abstract quotient theorem without a current substantial client would still have weak value.

### Cleared: RefinedPair formal descent through injective exponent dilation

Searches of placed reports/notes and all twelve archives found no proposal using `MvPolynomial.expand_injective`, `expand_two_core` and the radical-product identity to derive a universal polynomial identity and eliminate complex square-root choices in `RefinedPair.value_eq`. RefinedPair occurs in old source inventories only. Earlier rational-root descent proves integrality while retaining chosen roots; this proposed argument removes the root construction by injectivity of formal exponent substitution and is a different mechanism.

### Rejected or weak: binary-word coordinate decoding

An exact inverse projection formula `binaryWord f n / 2^j % 2 = f j` was not found. However I04 already supplies fixed-length digit injectivity and full-word recovery, so generic binary-word injectivity is not new. Applying that old theorem to the canonical bit vector of 510 would already remove most `binaryWord_510_bits` reasoning. The stronger quotient projection should be retained, if at all, only as a narrowly justified additional API whose marginal value survives that earlier injectivity result; it should not be a headline discovery by itself.

### Rejected: generic three-backend enumerator frontend

E section 14 already proposes a supplied-realizer backend for the direct/native graph enumeration control flow, retaining exact operation/witness counts. Adding the scalar backend is another instance of that old abstraction, not a new idea under the user's counterfactual baseline.

## Evidence limits

This audit is a mechanism-level comparison, not a proof that a phrase never appears in every byte of repository history. Reports and targeted notes were compared directly; source snapshots embedded in archives were not treated as newly proposed ideas merely because their old code contains a potential technique. Existing artifacts may validate old prototypes, but none of those old validation claims transfers to a new candidate. Before final reporting, each retained candidate should have its own exact mathematical statement, actual source target, closest earlier proposal, adapter obligations and validation status.
