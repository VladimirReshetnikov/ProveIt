# Scoped Part X publication review and six-archive intake

The previously missing Part X is now present in the Polish-arithmetic article. This review found no new fully costed finite Diophantine compiler in the material read. The added text concerns additive Presburger models, countable products, elementary embeddings and inherited Polish topologies. Its effective-normal-form and proof-assistant interfaces remain proposed work. No mathematical correction is requested within this review's limited scope.

This is a publication-transfer and computational-routing review, not certification of the entire article or of the six arriving manuscripts. Reading a proof for its hypotheses and routing consequences is not a claim to have independently established every infinite theorem it invokes.

## Immutable provenance and coverage

The publication comparison is exactly `c9bc70d8f0aa4ec095dad2f13f5c43b0ce7fd82d` against its parent `9fe62865dc30d71256183466b744b98ebf7e64d6`. Only the following three files changed under `Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic/`:

| File | Old SHA-256 | New SHA-256 | Read scope |
|---|---|---|---|
| `README.md` | `bd563be861542e62008126aea900aa1da26850c26ddf1173f40859031e387797` | `cda813d4a74a42865715142cfede455421dba33497170c5b5fd7af3d8254ce8c` | Full new text, lines 1–1010 |
| `article.tex` | `f311e9063087ab93cd95915f455e242c5e55c790c1de321826178553b089bc05` | `747b3394ef03fdb882fcea8b7378c7a47eedc59bc35453840e78ea0cb689e2da` | Entire 2512-line diff, including all added Part X and appendices |
| `article.pdf` | `72e765bb416be97084eeaf187ac2514d6b25bcfa06e217903aa8ff6cbaf13893` | `c790301cdbe5b97d28d908e272aa3db0cdfe34accc397c42e4e5b71cff7a0972` | Hash only; not rendered or rebuilt |

The companion JSON records exact Git blobs, sizes, old/new line counts, every changed hunk, all added labels and all archive member hashes. Human article coverage includes the front matter and old-question annotations, Part X at new lines 21202–22846, new provenance/nonclaim paragraphs, source-16 appendices at 25157–25319, and new bibliography entries. Unchanged Parts I–IX were not reread wholesale.

`Algebra/SurrealNumbers/AGENTS.md` was read in full, SHA-256 `ecf44fe89f365a1b88d7d5e94e23bf3ab6a713d01a4ee8c44f72f234a4295039`. The earlier `review_batch89_remaining_writes_e3e58a882.md` was read in full; the provenance, coverage and remaining-gap passages of `review_batch89_topology_23adb85f9.md` were consulted. Their hashes are in the companion JSON. These older reviews remain historical statements at their own commits.

The earlier `23adb85f9` placement supplied source-16 ancillary files; it did not yet put Part X into the article. The actual text write reviewed here is `c9bc70d8f`. The README's placement column records the ancillary delivery, while its current Part X column describes the now-published text. The new write resolves the exact absence recorded in the older review; it does not retroactively change that review's result.

## Transfer and label checks

The fresh label census gives 708 old labels and 784 new labels: 76 additions, no removals and no duplicate labels. The additions are the 55 delivered labels under `pma:emb:`, 16 additional labels within Part X, `pma:part:emb`, and four labels on existing Part I questions. Every delivered label is present after prefixing.

For that comparison the original archive was read as inert bytes at arrival `7c0f2d9f92c3d51ec85703bed1022924a4b7359b`:

- `docs/incoming/Glazer_ProveIt_Embeddings_and_Thresholds.zip`, SHA-256 `1aa1de81477be1aa90b57eb67d4bb3cb391c035914be79b1937fd5f0252824ec`;
- member `glazer_presburger_embeddings/glazer_presburger_embeddings.tex`, SHA-256 `d84f2ed25648e1481924d1f7b3f1ec9baa1be730ecdebed1e709fd7d08d62507`.

This original member received a label scan, not a fresh full-manuscript read or a word-for-word proof-transfer certification. PDF page counts, printed statement numbering, layout and every external cross-reference were not independently certified.

## Mathematical and computational scope of the added text

The carrier is `M_alpha = (Q^alpha ×lex Z)_{>=0}` for a countable ordinal `alpha`, with discrete rational coordinates and the product topology. The language is additive Presburger arithmetic. The maps preserve the unit; they are not arbitrary homomorphisms of rings. The coefficient space is the full product, not the finite-support sum. The continuous/Borel matrix statements use row-finite rational matrices with increasing positive pivots. These qualifications are preserved in the main statements and the new README summary.

The elementary-submodel classification is for this split rational-product family. Polishness refers to the inherited topology. Closed subspaces receive pivot normal forms and continuous left inverses. The lattice, ambient-orbit and self-copy claims do not classify arbitrary Polish Presburger presentations. The continuity threshold at `omega` and closed-image threshold at `omega*2` have different meanings, explicitly explained by the onto shear versus shifted graph construction. Negative examples use a Choice-built functional annihilating finite-support vectors; finite rational tests cannot detect that functional.

The new `pma:emb:rem:choice` is additional merge mathematics, not part of the 55-label delivery. Its argument identifies a discontinuous coordinate functional whose countable-index kernel lacks the Baire property; the countable choices are consistent with its ZF+DC premise. I checked the cited consistency input at the primary source: Shelah's [published paper, Conclusion 7.17, p. 43](https://shelah.logic.at/files/95333/176.pdf) states equiconsistency of ZFC with ZF+DC plus the Baire property for every set of reals. The bibliographic entry also matches the [author's publication record](https://shelah.logic.at/papers/176/). This is a bounded statement/dependency check, not an audit of Shelah's forcing proof or a new weak-choice equivalence theorem.

The omnific realization is additive and order-preserving on a fixed set-sized support. The coefficient topology is transported to that image; ring closure and a topology on the entire surreal proper class are explicitly disclaimed. The conventional quantifier-elimination appendix correctly keeps complete congruence-class invariance distinct from iteration of one standard shift in a nonstandard group.

The new computation-facing material does **not** provide a finite ordinary-input universal polynomial:

- Finite ancestry makes each inverse coordinate depend on finitely many predecessors. It does not provide a single finite circuit for a countably infinite matrix or a bound on its arithmetic cost.
- `pma:emb:q:effective` asks for hypotheses enabling effective pivot sets, reduced coefficients and inverse rows. `pma:emb:q:computable` asks for effective well-founded recursion and quantified inverse-row cost. These are questions, not implemented compilers.
- The six modules in the formalization route are a plan. The existing integer Presburger procedure is explicitly not treated as a formalization over arbitrary nonstandard Z-groups. No new Lean or Rocq implementation is claimed.
- The reported 11,243 finite rational checks are the delivery/publication authors' evidence. This review did not run them. They concern finite examples and do not establish the infinite normal-form, category, elementarity or Choice statements.

Part VIII's older ATR_0 claim remains marked unreviewed in the new README. The added Part X does not upgrade that claim or add a costed MRDP/exponentiation implementation. No claim about the current arithmetic 84-gate boundary follows from this publication.

## Six arrivals: exact bounded intake

All six archives were read at immutable arrival `a162e4386fa8a1beaef58a565c2205ba5fb5c270`. The inventory hashes all 53 non-directory members. All six delivery READMEs and the hat verifier's additional README were read in full. Hashing the remaining members does not mean their contents were reviewed.

| Archive | ZIP SHA-256 | Members | Human-read routing result |
|---|---|---:|---|
| `Named_Symmetries_and_Replacement.zip` | `7e74dc205154d4ff96514fe80ff387e228b6604555c346a92881e96accbff0f9` | 8 | Finite-atom-kernel Replacement and named symmetry hierarchy; finite centralizer diagnostics, no arithmetic compiler in the README |
| `Perfect_Transcendence_Gaps_Package.zip` | `c609ba5a42ffa6420a53a28e0af0742841d7066383827d1c736fbd12c8d3cfe9` | 8 | Perfect independence gaps, standard systems and canonical p-adic/profinite images; potentially relevant coding boundaries, no paid polynomial source in the README |
| `Surreal_Subfield_Cantor_Research.zip` | `98e30d2665ba775c744f51d963b2809e6c18f2e198ca63f5562998e8c657344c` | 9 | Analytic-complete embeddability inside a countable surreal field and finite-support topology; descriptive complexity is not finite arithmetic universality |
| `glazer_proveit_topology_research.zip` | `09b1fa9917baa178e70164c5afe2e535a14a5f470c1373f54835459117798a69` | 7 | Claims a group-completion criterion using continuous partial subtraction and class-manifold size results; follow-up for the older completion question, proofs unreviewed here |
| `hat_guessing_research.zip` | `f82db269d8c6b6138a55fc9b6effd4eccd194f115588b82ba06b92b0cedfde81` | 14 | Finite-dependence hat strategies and asymptotic surplus; finite XOR/parity diagnostics have size-dependent exhaustive scope, no paid Diophantine source in the READMEs |
| `local_geometric_codes_research.zip` | `d81335937ec31ca59860ae1de8586f77a83062a89527f5d572dd962d4738a54e` | 7 | Closest arithmetic-coding lead; conditional local-code topology theorem, with code existence and conversion obligations retained |

The README member/range coverage is exact: named symmetries `README.md` 1–71; perfect gaps `README.md` 1–125; surreal subfields `README.md` 1–86; topology `README.txt` 1–71; hats delivery `README.txt` 1–91 and `code/README.txt` 1–85; local codes `README.txt` 1–105. The companion JSON gives their full archive member paths and SHA-256 values.

Only the last archive received further mathematical text reading. `local_geometric_codes/local_geometric_codes.tex` was read at lines 76–267, 401–437, 1287–1390, 1573–1916 and 2103–2255, with a heading/claim search elsewhere. `local_geometric_codes/PROOF_STATUS.txt` was read in full, lines 1–126. These selected spans cover its headline hypotheses, beta decoder, certificate/domain conclusions, metatheory, proposed formalization/recoding and diagnostic limits; they do not cover the full metric/category proof.

The code is `beta(u,v,i) = rem(u,1+(i+1)v)`. The main theorem assumes one already existing internal code with initial value 1 and recurrence `beta(i+1)=q*beta(i)` for **every** internal `i<C`. It concerns an `I Delta_0` model with a Polish carrier and Borel arithmetic, and external uncountability/discontinuity. The finite parameter tuple does not itself replace the bounded universal recurrence by a fixed existential polynomial.

The stronger Borel-certificate conclusion is obtained after a separate-continuity hypothesis forces all valid lengths into a countable core. The text explicitly does not infer Borelness from bounded syntax alone. It gives a local ATR_0 upper-bound argument under coded interfaces, separately from its ZFC global consequences; this review does not certify that reverse-mathematical argument. Ordinary partial exponentiation has not been identified with the existence of full beta certificates. Code extension/concatenation, general recoding and uniform effective Borel ranks remain unprovided. Its finite CRT cases through length 9 are expressly diagnostics, not a proof of arbitrary internal code existence.

Accordingly, this archive is useful for clarifying conditional code interfaces but supplies no new paid arithmetic bound in the spans read. The remaining five archives are routed from their READMEs only; no absence claim is made about unread proofs or code. The new group-completion claim merits a separate future proof review rather than silently treating the old open-question language as a theorem defect.

## Execution and reproducibility boundary

No supplied, archived or frozen program was executed or imported. No Lean, Rocq, LaTeX or PDF build was run. No repository file or Git state was changed. Fresh standard-library scratch operations used read-only Git bytes, ZIP decoding, SHA-256 and label/hunk scans; all writes were under `/tmp`. The stored delivery check results were not replayed or promoted to reviewer evidence.

The companion receipt is `review_polish_partx_c9bc70d8f.json`, SHA-256 `3eb296146ce0233db75deb835e7568ace428f247399e6252a1131bd570e290f8`. It is a provenance and read-scope manifest, not a full-manuscript correctness certificate.
