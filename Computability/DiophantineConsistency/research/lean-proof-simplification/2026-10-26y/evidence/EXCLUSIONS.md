> Closing refresh: see CLOSING_AUDIT.md and closing-audit.json for the exact-content continuity check and the three additional packets at e652d21c413de59e4821f6e8e9b6a3a077bf5bfe. The original audit below preserves its initial snapshot provenance.

# Exclusion audit for the new proof-simplification report

Snapshot: `553a5f7a463cbaab8800ff8148fef0bc5a9e1b22`.

## Scope and method

The direct corpus consists of six placed packets (a-f) and the twelve ZIP archives currently in `docs/incoming`. Every ZIP was opened as inert data. Cached copies were accepted only after their Git blob hashes matched the pinned GitHub API metadata byte for byte. No old proposal script was executed. The archive manifest records all 2,405 ZIP members and all 323 files in the placed corpus; 2,067 ZIP members have relevant text extensions. These are inventory counts, not counts of distinct ideas or claims that every member was read line by line. The report bodies and relevant source notes, prototypes, optional suggestions, and existing novelty ledgers were surveyed; targeted searches were used to test each new candidate.

The broad incoming README was inspected for routing and scope. This audit does not claim to re-read all historical mathematical reports transitively linked by that README. New-idea wording should therefore be: **not found as a proposal in the audited six placed packets and twelve current incoming archives**.

All old proposals are excluded whether adopted, pending, deferred, or uncompiled. Implementing an old proposal is new validation, not a new proposal. Main report headings alone are insufficient: the audit includes optional and unselected suggestions in notes, including the support-frame API, schema-renaming normalization, cyclic packing algebra, finite support membership API, and modulus-instance cleanup.

## Source key for S01-S25 and A01-A31

- A: placed packet a, `report.tex` and `source_notes/`.
- B: placed packet b, `report.tex`.
- C: placed packet c, `report.tex` and `notes/`.
- D: placed packet d, `report.tex`.
- E: placed packet e, `report/report.tex`.
- F: placed packet f, `report/sections/` and `inventory/INVENTORY.md`.
- G: `diophantine-lean-simplification-2026-10-26(1).zip`.
- H: `lean-proof-simplification-review-2026-10-26.zip`.
- I: `diophantine-lean-new-ideas-2026-10-26.zip`.
- J: `diophantine-lean-additional-simplifications-2026-10-26.zip`.
- K: `diophantine-lean-new-directions-2026-10-26.zip`.

The first 56 grouped rows reconcile the older residual packet's detailed exclusion ledger with the primary sources. The final 27 add more recent direct-corpus proposals. They deliberately include nearby variants so the same mechanism cannot be counted under a new name.

## Grouped exclusions

| ID | Existing idea family | Evidence |
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
| S26 | Reuse total bounded table decoding to prove the raw parent-checker characterization. | ProveIt_Lean_Simplification_Round2_2026-10-26.zip :: LeanReview2/report/sections/03_parents.tex |
| S27 | Consume a Boolean certificate before building its conditional, preserving the supplied program. | additional_lean_simplifications_2026-10-26.zip :: report/additional_lean_simplifications.tex, Consume the Boolean certificate before constructing a conditional |
| S28 | Collect proof fragments for any list of premises, with ambient-history-stable parent indices. | lean-proof-simplification-new-2026-10-26.zip :: report.tex, B: construct proof fragments for any number of premises |
| S29 | Prove fork-certificate transport at successor outputs, isolating output zero once. | lean-proof-simplification-new-2026-10-26.zip :: report.tex, C: prove fork certificates at successors first |
| S30 | Strengthen quadratic Nat pairing certificates to canonical selector/slack/maximum witnesses. | lean-proof-simplification-new-2026-10-26.zip :: report.tex, E: pairing certificates have canonical witnesses |
| S31 | Define one rule-schedule syntax and derive both numeric evaluation and supplied-PR programs. | lean-simplification-residual-2026-10-26.zip :: report.tex, Define rule schedules once and derive both interpretations |
| S32 | Specialize binary graph composition-depth bookkeeping once for Fin 2. | ProveIt_Lean_Simplification_Round2_2026-10-26.zip :: LeanReview2/report/sections/09_supplemental.tex, S2 |
| S33 | Replace repeated finite support insertion cases by an explicit membership specification or indexed support representation. | 2026-10-26f/inventory/INVENTORY.md:53; targets NativeQuadraticPositions |
| S34 | Centralize common positive-modulus NeZero instances and cast/divisibility normalization. | 2026-10-26f/inventory/INVENTORY.md:54 |
| A32 | Compare Pell bases by simultaneous monotonicity of the positive pair recurrence; avoid exponential detours. | diophantine-lean-new-simplifications-2026-10-26.zip :: Idea 4; lean-simplification-residual-2026-10-26.zip :: Compare Pell bases through the positive pair recurrence |
| A33 | Use a natural-number perturbation kernel and power-sandwich theorem for both Pell upper estimates. | lean-simplification-residual-2026-10-26.zip :: A natural-number perturbation kernel for both Pell upper bounds |
| A34 | Parameterize the common Pell ratio estimate by its explicit error factor. | lean-proof-simplification-new-2026-10-26.zip :: A: one Pell estimate with an explicit error factor |
| A35 | Recover the half-binomial through an exact integer quotient and rounding theorem. | lean-simplification-residual-2026-10-26.zip :: Recover the half-binomial value through an exact integer quotient |
| A36 | Use a general small-ordinate Pell fundamental-unit criterion, with y <= 3 sharp. | additional_lean_simplifications_2026-10-26.zip :: A uniform small-ordinate criterion for Pell minimality |
| A37 | Replace object-natural zero-sum/product inductions whose hypotheses are unused by internal zero-or-successor decomposition. | diophantine-lean-new-simplifications-2026-10-26.zip :: Idea 1; diophantine-lean-post-roadmap-2026-10-26.zip :: Delete internal inductions whose hypotheses are unused |
| A38 | Prove nonsquare norm nonvanishing entirely over integers through equal-power divisibility and cancellation. | diophantine-lean-new-simplifications-2026-10-26.zip :: Idea 5: prove the norm fact entirely over the integers |
| A39 | Exclude a negative Pell unit by squaring it and using positive-unit classification plus a congruence invariant. | diophantine-lean-post-roadmap-2026-10-26.zip :: Derive the negative Pell obstruction from positive units |
| A40 | Normalize shifted/squared negative-norm obstructions to the existing ShortEquation theorem. | diophantine-lean-post-roadmap-2026-10-26.zip :: Normalize three residue obstructions to one existing theorem |
| A41 | Extract exact minima of all coupled blocks from equality of aggregate lower bounds. | diophantine-lean-post-roadmap-2026-10-26.zip :: Extract all block equalities from one minimum-saturation theorem |
| A42 | Share empty/union/insertion/extraction laws of monotone local certificates over an arbitrary model-set membership interface. | diophantine-lean-post-roadmap-2026-10-26.zip :: Optional: a calculus for monotone local certificates |
| A43 | Recognize a physical shift permutation as the existing positive tail. | additional_lean_simplifications_2026-10-26.zip :: Optional: recognize the physical permutation as a positive tail |
| A44 | Use binaryWord_prefix directly for the two South shift clients, preserving exact weighted correction. | Lean_Proof_Simplification_New_Deltas_2026-10-26.zip :: section 4; ProveIt_Lean_Simplification_Round2_2026-10-26.zip :: section 06_south_prefix |
| A45 | Use theta as the exact aligned-cell reachability difference witness and specialize existing propagate_from at zero. | Lean_Proof_Simplification_New_Deltas_2026-10-26.zip :: section 5; ProveIt_Lean_Simplification_Round2_2026-10-26.zip :: section 05_finite_and_cycle |
| A46 | Consolidate exact high North/South color classifications into equality-indexed fibers or a NorthView. | Lean_Proof_Simplification_New_Deltas_2026-10-26.zip :: sections 6-7; ProveIt_Lean_Simplification_Round2_2026-10-26.zip :: section 08_north_view |
| A47 | Characterize an alternate marked assignment by selector bits in the same original word, then transport correctness. | Lean_Proof_Simplification_New_Deltas_2026-10-26.zip :: section 8 |
| A48 | Hoist binaryWord_congr beside its definition and use it for copy translation and horizontal bit aggregation. | ProveIt_Lean_Simplification_Round2_2026-10-26.zip :: section 07_word_congruence |
| A49 | Use the explicit CRT residue already in context instead of search in BoundedForallCertificate. | ProveIt_Lean_Simplification_Round2_2026-10-26.zip :: section 09_supplemental, S1 |

## Additional local edits already excluded

Carrier66 positivity coordinate proofs, canonical-zero focused simplification, shared Gates.complete branches, ArithmeticDAG.run_map cleanup, whole-conclusion exact_mod_cast, half_base_bound_31 specialization, Finset filter/intersection identities, predecessor-power cancellation, Nat.one_lt_two_pow, convolution distributivity, finite-switch complement, pure axiom-wrapper generation, and import/profiling methodology are prior work. They are not additional new ideas for the present report.

## Candidate decisions in this review

| Candidate | Decision | Nearest prior and required distinction |
|---|---|---|
| Pell congruence modulo sign | Exclude | I and K already give precisely the relation/transitivity/natAbs mechanism. |
| Reuse odd_index_of_base_dvd | Exclude | I, additional_lean, and new-simplifications already give the exact NativePellStepDown application. |
| Remove real half-binomial arithmetic | Exclude as a headline | Residual packet already provides natural perturbation bounds and exact integer quotient rounding; the scaled estimate is also prior. |
| Internal formula-code catamorphism | High overlap; exclude without a demonstrably distinct theorem | K explicitly proposes definable recursive-algebra folds, constructor unique existence and graph fusion; post-roadmap supplies local certificate algebra. |
| Function.Periodic/additive translation period calculus for HelicalQuotient | Provisionally distinct | Prior cell propagation is finite invariant transport; no period-stabilizer, zsmul, or helical quotient proof proposal found. Original bundled WangTiles942Periodic uses periodicity, so do not claim the concept is absent from the repository. |
| Seam-gluing a trace path into a finite cyclic tiling | Provisionally distinct | No TraceCycle, boundary-path or seam-gluing proposal found. Must replace actual cyclic-boundary reasoning rather than rename generic history invariants. |
| Internal-natural LinearOrder from strict total order | Provisionally distinct | No strict-order reconstruction proposal or linearOrderOfSTO/IsStrictTotalOrder mention found. Preserve the current <= definition or prove adapter compatibility. |
| Max-square pairing branch recovered from output threshold | Provisionally distinct | Prior pairing graph/canonical-witness proposals recover witnesses from input order. Threshold recovers branch from common output and maximum in the abstract semiring, a different obligation. |
| NativeQuadraticPositions.index_span via extremal-row pruning | Provisionally distinct | F already suggests support-membership certificates. The new argument removes support reasoning entirely for rows 0-20, retaining only row21's five entries. Must show this survives after the earlier membership API is assumed applied. |
| Initial-strip seam gap `L + R <= N` and geometry-only period obstruction | Provisionally distinct | No seam-gap/strip-width/period comparison proposal found in placed a-f or the twelve incoming archives. Current source proves only the weaker period > 2 using actual machine soundness; new argument translates the left seam by one horizontal period. |

These are novelty decisions, not proofs of correctness or integration. Parent review must update status after testing the exact candidates. Novelty concerns the mathematical mechanism, not the use of a different tactic or wrapper name.
