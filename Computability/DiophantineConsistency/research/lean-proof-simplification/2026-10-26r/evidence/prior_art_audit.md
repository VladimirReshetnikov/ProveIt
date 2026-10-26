# Prior-proposal exclusion audit

Snapshot: `9bd29079d5e1c6cc1c0bcaee6cb57d59b835cba9`, reviewed 26 October 2026.

## Scope and audit method

The direct exclusion corpus has six placed packets, `2026-10-26a` through `2026-10-26f`, and five ZIPs still present in `docs/incoming`. All five ZIPs were opened as inert data. Their text members were extracted into a temporary research directory; no supplied code was executed. The earlier archives themselves are not redistributed in this packet. Reports, READMEs, substantive source notes, novelty audits, proposed interfaces, and relevant Lean artifacts were surveyed. This audit includes ideas mentioned in notes, optional research directions, and unselected candidate lists, rather than limiting exclusion to report headlines. Exact source/member hashes are in `prior_corpus_manifest.json`.

The long `docs/incoming/README.md` also indexes historical projects and reports outside the two requested directories. It was inspected for relevant routing and scope; this audit does not claim to reread every manuscript transitively linked by that index. Novelty wording should be scoped to the directly inspected DiophantineConsistency simplification corpus.

All these proposals are treated as already applied, as the user requests. `ADOPTION.md` records actual adopted/pending/deferred distinctions, but those statuses do not change this exclusion test. Compiling an uncompiled old idea would be new validation, not a new idea.

## Exact source key

Let `P = Computability/DiophantineConsistency/research/lean-proof-simplification/`.

| Key | Exact path or archive member | Main content |
|---|---|---|
| A | `P/2026-10-26a/report.tex`; `source_notes/{checker,circuits,digits}-review.md` | Initial proof-engineering portfolio; several recommendations appear only in source notes. |
| B | `P/2026-10-26b/report.tex` | Witness layouts, history folds, circuit certificates, native arithmetic, model boundaries. |
| C | `P/2026-10-26c/report.tex`; `notes/{syntax,arithmetic,circuits}.txt` | Coefficient schemas, shared tail, row operations, proof-fragment composition. |
| D | `P/2026-10-26d/report.tex` | Assignment naturality, coefficient envelopes, finite pushforward, cyclic residues. |
| E | `P/2026-10-26e/report/report.tex` | Euclidean certificates, guarded solution transport, shared graph control flow, local algebra. |
| F | `P/2026-10-26f/report/sections/{00_summary,02_local,03_architecture,04_circuits}.tex` | Local specializations, nine-coordinate packaging, named contexts, typed circuit views. |
| G | `docs/incoming/diophantine-lean-simplification-2026-10-26(1).zip`, member `diophantine-lean-simplification/report.tex` | Assignment/witness split, sum-at-most-one, scanner/circuit certificates, origin corrections, internal arithmetic. |
| H | `docs/incoming/lean-proof-simplification-review-2026-10-26.zip`, member `lean-proof-simplification-review/lean-proof-simplification-review.tex` | Decoder Option proofs/fusion, residuals, casts, coefficient compression, object endpoints. |
| I | `docs/incoming/diophantine-lean-new-ideas-2026-10-26.zip`, member `diophantine-lean-new-ideas-2026-10-26/report.tex` | One-hot, Pell parity, inverse-product projections, Euclidean certificate, affine budgets, sign relation. |
| J | `docs/incoming/diophantine-lean-additional-simplifications-2026-10-26.zip`, member `diophantine-lean-additional-simplifications-2026-10-26/report.tex` | Rational root descent, units, exact decoder graph, finite invariant predecessor, support envelopes, point-mass convolution, `fun_prop`, canonical normalization. |
| K | `docs/incoming/diophantine-lean-new-directions-2026-10-26.zip`, member `new-lean-simplification-2026-10-26/report.tex` | Decoder graph, sign orbits, internal constructor views/unique existence, definable graph fusion, depth certificates, explicit carries. |

## Exclusion map: structural and compiler ideas

| ID | Already proposed family | Concrete source pointer |
|---|---|---|
| S01 | Replace list lookup/membership inductions with core `List.getElem?` API; Option map injectivity. | A §Use the core list-lookup API; E §6; H §Seven list inductions. |
| S02 | Congruence under `Nat.rec`; shared axiom-free recursor congruence; optimizer correctness through recursor equality. | A §Rewrite under primitive recursion and `lean/RecursorCore.lean`. |
| S03 | Assignment naturality under `Sum.map`, renaming/evaluation transport, witness-block splitting and regrouping. | A assignment patch; B §Witness layouts; D §Assignment naturality; G §Assignment transport; H §Assignment-transport API. |
| S04 | Move constructor projection/witness-count lemmas earlier in imports. | B §Move existing projection lemmas to their natural home. |
| S05 | Shared scanners via iterate/fixed point/successor/zero laws, arbitrary raw-code soundness and encoded-list simulation. | A §Scanner proofs; B §Checked histories; C §Share scanner proofs; G common scanner kernel. |
| S06 | Supplied `iterateFrom`/`iterateProgram` combinator with seed/fuel/step, retaining literal programs and counts. | B §A better primitive-recursive iterator interface; C §Factor the supplied PR iterator. |
| S07 | Guarded/validated history fold, append/invariant laws, `Produces.append`/`Produces.step`, and certified fragment composition. | C `notes/syntax.txt` §3 explicitly names `ready_binary`, `ready_unary`, `fragment2`, `fragment3`; B §One invariant-preserving history fold. |
| S08 | Exact numeric Boolean output rather than range + acceptance iff; common finite tag dispatch. | A §Replace acceptance equivalences by exact numeric values; B §Share tag dispatch. |
| S09 | Shared sum-of-squares evaluation/zero iff/degree/cost API across compilers; five-square criterion. | A §Sums of squares; C §Share residual-system facts; H §Finite residual and degree arguments. |
| S10 | Generic semiring gate correctness, natural compiler specialization, identical branch merging. | B §The semiring theorem already subsumes the natural induction; E §5. |
| S11 | Topological `run_invariant` for DAG evaluation, uniqueness, nonnegativity, and degree. | A §Shared induction for topological circuit semantics; C §Common DAG invariant; H §Reusable invariant. |
| S12 | Existing `run_power` with exponent labels; finite certified node dispatch; generated helper templates/indexed facade/lazy node facts. | A/B/F generated circuit sections; H §Generated circuit interfaces. |
| S13 | Reuse semantic register cuts; common 99-node free-carrier tail; block certificates preserving embedding. | C §Use established register facts / shared 99-node tail; E §9/11; F §Certify semantic blocks. |
| S14 | General circuit translation/simulation; commuted add/mul node relations. | A §Treat commutative swaps; C §Translation/reflection interfaces. |
| S15 | Register append invariants, old/new-index frame facts. | A §Package append invariants locally. |
| S16 | Move structural/weighted-degree machinery earlier; shared RHS degree bound; degree profiles/prefix; cancellation-sensitive proofs. | A/B/C compiler sections; F §Shared degree profiles and ShortSystem prefix. |
| S17 | Checked/typed circuit wrapper with topology/output index; dependent SafeNode operands; erase to unchanged literal list. | F §Treat typed circuit views as a later design option. |
| S18 | Nine-coordinate existential packaging preserving slot 7, named accessors for long conjunctions, coherent source/window certificate. | F §Simplify the interfaces between proofs. |
| S19 | Shared direct/native graph-enumerator control-flow builder, preserving different cost models. | E §14 Share control flow without collapsing cost models. |
| S20 | Exact decoder graph, fused quotation/depth induction, Option-based independent constructive variants. | H §Shorten decoder proofs; J §Describe tree decoder by exact graph; K §Fuse syntax-decoder correctness. |
| S21 | Inverse coordinate graph obligations from one product-equivalence/pairing theorem, preserving data. | I §Derive inverse graphs from a product equivalence. |
| S22 | Shared affine witness/depth budget, automated max-plus representation-depth certificate synthesis. | I §Factor arithmetic budget; K §Synthesize representation-depth bounds. |
| S23 | Automate extensional `Primrec` closure with registered `fun_prop` rules. | J §Automate extensional primitive-recursiveness composition; notes/checker.md. |
| S24 | Support-restricted evaluator congruence plus overwrite/frame rules. | K `evidence/prior_ideas.md`, unselected candidate 7; notes existing `WitnessCompaction.eval_congr`. |
| S25 | Certified normalization of `AnnotatedSchemaMaps.rsep/rf1/rf2/ri` renaming-map composition. | K `evidence/prior_ideas.md`, candidate 8; `evidence/semantic_review.md` §5. |

## Exclusion map: arithmetic, native encodings, and object theory

| ID | Already proposed family | Concrete source pointer |
|---|---|---|
| A01 | Half-radix/scaled division exact identity replacing finite enumeration; quotient/residue consequences. | A/B/C/D half-radix sections. |
| A02 | Derive weaker modulus facts by divisibility from strongest congruence. | A modulus-reuse patch; C/D cyclic residue sections. |
| A03 | Conditional padding witness, eliminating dummy branch witnesses. | A §Make the padding witness conditional. |
| A04 | Exact digit/carry decomposition API; derive recurrence/reset rather than store duplicate data. | A §Use one exact decomposition interface; B §Derive recurrence; C current-window API. |
| A05 | Common aligned-cell cyclic geometry, wrapped shifts, residue/offset/off-origin mask facts; aligned cells equivalent to `ZMod N`. | A digits-review §5; B §Share physical-field residues; D scaled division/cyclic residue. |
| A06 | No-borrow origin decrement; origin-correction common lemma for mask families. | A digits-review §6; G §One origin-correction lemma. |
| A07 | Expose direct physical selector-sum identity; avoid prefix sum round trips. | A digits-review §7. |
| A08 | Restored canonical source/window extraction with coherent shared witness; small WordFacts contexts. | A digits-review §8; E §12; F architecture sections. |
| A09 | Finite-fiber pushforward identity for folded stencils; separate arbitrary folding and injective sparse placement. | D §One finite-fiber identity; G folding section. |
| A10 | One coefficient-row envelope proof, narrow finite dispatcher, sparse normalizer, nonnegative monomial majorant certificates; row naturality. | C coefficient sections and notes; D coefficient envelopes; H coefficient certificate section. |
| A11 | Elementary row operations and surjective row reindexing preserve simultaneous zero sets. | C §Represent elementary row operations once. |
| A12 | Decode source/Pell row equations once; share Nat/Int boundary conversion. | B §Decode source-register equations once. |
| A13 | Generic finite chunk assembly/dispatch retaining checked leaves; copied-field descriptors/bounds; mask block reuse. | B Carry certificates/finite data assembly; E §13. |
| A14 | Guarded existential solution transport and same-domain zero-set congruence, preserving domains rather than demanding inverses. | E §10; G §Lift pointwise zero-set equivalence once. |
| A15 | Guarded Euclidean quotient/remainder/slack certificate shared across Register/Quadratic backends, including uniqueness. | E §6; I §Positive-denominator Euclidean certificate. |
| A16 | One-hot finite support classification using `Finset.sum_le_one_iff`. | G §Use existing sum-at-most-one API; H §Finite sum at most one; I §Finite-support classification. |
| A17 | Existing Pell odd-index criterion; remove redundant natural-to-integer cast witnesses in residue uniqueness. | I §Reuse already proved Pell parity; H §omega cast interface. |
| A18 | Congruence up to sign as transitive relation/orbit, negation and natAbs transport, deferred half-interval sign resolution. | I §Make congruence up to sign compositional; K §Treat Pell sign ambiguity. |
| A19 | Preserve rational roots while proving integrality, descending the full witness tuple without fresh sign choices. | J §Preserve rational roots when descending to integers. |
| A20 | Decompose a product's units at once instead of sequential factor proofs. | J §Decompose the product's units once; earlier E includes narrower unit algebra. |
| A21 | Recover invariant predecessor by finite invariant-subset bijectivity. | J §Use finiteness to recover an invariant predecessor; notes/finite-invariant.md. |
| A22 | Polynomial support envelope/degree bound before individual coefficient arguments. | J §Prove support envelope before individual coefficients. |
| A23 | Rotation as convolution with a point mass. | J §Rotation is convolution with a point mass. |
| A24 | Canonical carry normalization uniqueness by finite maximum principle, with entire packed word fixed. | J §Canonical normalization from finite maximum principle. |
| A25 | Closed-form least/greatest cyclic carries via rotated weighted sums, exact two-solution ambiguity, budget picks least carry. | K §Explicit cyclic carries; algebra_review/peer_review_carry. |
| A26 | Cyclic packing as algebra homomorphism from additive monoid algebra on `ZMod n` to `ZMod(radix^n-1)`, deriving convolution and rotation. | K `evidence/algebra_review.md` optional direction and `prior_ideas.md` candidate 9. |
| A27 | Definable induction transport with actual formula witness over arbitrary internal naturals. | A §Definable-induction transport; C/E object sections. |
| A28 | Shared model-to-ZF-axioms and validity/completeness/sealing bridge, arity-polymorphic closed-sentence transport. | A/B/C/D/H object-layer sections. |
| A29 | Internal constructor views/inversion, combining totality and uniqueness into one definable `∃!` induction. | K §Constructor views and one internal unique-existence induction. |
| A30 | Definable recursive graph preservation and fusion (`ThetaG`), stage-formula adapters. | K §Preservation and fusion for internal recursive graphs. |
| A31 | Share model-independent finite-index/row-family proofs with internal-natural arithmetic, retaining definability. | C notes/syntax §6; G §Finite-index reasoning in object layer. |

## Small local suggestions also already covered

F explicitly proposes specializing `half_base_bound_31`, Finset filter/intersection support identities, predecessor-power cancellation, `Nat.one_lt_two_pow`, convolution distributivity normalization, and one finite-switch complement proof. E already includes simplifying Carrier66 positivity coordinate proofs, narrow canonical-zero rewrites, `Gates.complete` alternative constructor branches, `ArithmeticDAG.run_map`, and `exact_mod_cast` on the whole Pell disjunction. These should not be counted anew.

Generic profiling, narrow `simp only` sets, preserving semantic cuts, measuring source versus elaboration separately, generated proof templates, certificate sharding, import hygiene, axiom audits, compatibility wrappers, and regression controls are ubiquitous and are methodology rather than new contributions here.

## Concrete overlap decisions issued during this audit

1. **Signed modular orbit relation:** reject as new; I and K already implement exactly this mechanism, including natAbs.
2. **Fused exact decoder graph:** reject as new; H/J/K already supply variants, with K's exact decoder prototype and patch.
3. **Generic certificate forest/fragment assembler:** high overlap/reject as headline; C notes explicitly cover fragment2/fragment3 composition. A genuinely different stronger theorem would need clear independent content.
4. **Central-binomial integer rounding:** no substantive proposal found in this corpus. Existing Euclidean/carry identities do not target replacing NativeHalfBinomial's real Pell-ratio rounding by an exact binomial quotient argument. Candidate requires source and mathematics review.
5. **Single-source rule schedule DSL generating numeric and supplied-PR definitions:** no substantive prior proposal found. G report warns that merely metaprogramming the existing 17 short coordinate proofs is unhelpful; a new design must remove duplicated definitions/program construction and prove preservation, not repackage `fin_cases; rfl`.

## Required framing for the final report

Use “not found in the audited six placed packets and five current incoming archives,” not “never previously proposed.” Include the nearest old proposal for each new idea and explain the distinct mathematical obligation or duplication it removes. Do not claim savings relative to unchanged old code when the user's counterfactual says earlier abstractions are already applied. Helper overhead, adapter costs, and proof status must remain explicit.
