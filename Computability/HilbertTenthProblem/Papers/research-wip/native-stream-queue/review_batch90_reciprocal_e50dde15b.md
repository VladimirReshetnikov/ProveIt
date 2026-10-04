# Bounded review of batch-90 reciprocal notes, e50dde15b

**PASS within the recorded scope; no concrete correction requested.** Reviewed immutable commit `e50dde15b32a2416429af32cc7c0b71cba910f71` against parent `73e6615101628a34f8fff67ae1cc2a3fe435df1d`. This is a review of the added reciprocal notes and their selected source interfaces, not certification of all underlying manuscripts or externally cited theorems.

## Read and byte scope

All **23 changed text files** were read as complete raw unified diffs: 13 `README.md` files and ten `article.tex` files, across 13 report directories. The diff contains **321 added and 13 deleted text lines**. All **33 changed files**, including ten PDFs, have before/after Git blob IDs, byte lengths and SHA256 pins in the companion JSON. The PDFs were not rendered or read.

The JSON records each complete raw-diff read span and each corresponding before/after source hunk, with inclusive one-based line numbers and raw/normalized span hashes. Reading those hunks does not constitute reading each entire README or article. Selected target source spans are separately enumerated and pinned. Applicable `Algebra/SurrealNumbers/AGENTS.md` was read in full; its working bytes match the immutable commit.

All **46 complete label strings occurring in added diff lines** resolve uniquely in the checked target articles. This census includes references repeated when an existing long paragraph was modified: **31** newly occur in at least one changed file, so 46 is not a count of newly invented references. Namespace-only strings such as `hset:ns:` are excluded. All **11 added relative Markdown link occurrences** resolve to a file or directory in the commit. These checks do not independently reconstruct every printed theorem number or check every external URL.

All ten changed articles retain exactly their ordered label-definition sequences, including optional typed labels:

| Article | Before and after |
|---|---:|
| birthday-cutoffs-and-hereditary-sets | 372 |
| definable-surreals-and-omnific-integers | 139 |
| foundations | 265 |
| polish-models-of-omnific-arithmetic | 923 |
| surreal-fields-across-universes | 286 |
| surreal-well-orders | 1876 |
| independent-surreal-copies | 275 |
| omnific-diophantine-geometry | 553 |
| surreal-self-embeddings | 468 |
| naming-elementary-embeddings | 66 |
| **Total** | **5223** |

The remaining changed guides are `tail-spans-and-differential-transcendence`, `open-query-membership-games`, and `non-baire-translation-invariant-ideal`; their articles are not changed by this commit. The unchanged label census does not certify the new PDF builds or their printed page/theorem numbering.

## Mathematical scope checks

**Named atoms and Replacement.** The finite-cutoff comparison is correctly confined to finite *actual atom kernels*. In `birthday-cutoffs-and-hereditary-sets`, the setup at lines 6562–6627 uses an ambient well-founded universe with Choice and a uniformly named action of a pure set-sized group. It is not a theorem about the supports of an arbitrary Fraenkel–Mostowski model. The full criterion at 6747–6788, fixed-output-kernel levels at 6803–6833, single-permutation examples at 6869–6910, and two-involution hierarchy at 6956–6987 support the added comparisons. Every fixed level holding is explicitly distinguished from a varying output bound.

The language comparison at 7016–7138 is valid for finitely many named permutations and their canonical hereditary lifts; arbitrary infinitely many separate names need not supply a uniform evaluator. Pure-valued Collection is explicitly distinguished from full Collection, which already fails in the finite-kernel reduct. The selected `naming-elementary-embeddings` statements at 492–540, 600–624 and 738–827 confirm that its full Replacement, robustness, Collection and reflection results concern finitely many named injections at their stated cutoffs. The added “answered in part” annotations retain these restrictions and leave the broader group/evaluator questions open. No global equivalence of the two manuscript families is asserted.

**Class manifolds and native surreal topology.** The `polish-models-of-omnific-arithmetic` setup at 26359–26458 retains Set Choice, specified class comprehension, class Replacement and class Separation; it does not assume Global Choice, and omitting Foundation does not assert its negation. Its class-space notion is locally small with set basic opens. The manifold definition at 26760–26819 assumes **positive finite dimension** and Hausdorffness, so the continuum-cardinality statement is not being applied to zero-dimensional discrete manifolds. The injection/surjection transport theorem and birthday corollary at 27035–27222 give a bound for each specified carrier, not one uniform birthday bound for all carriers. The broader Glazer question remains a question at 27343–27378.

The notes distinguish this real-class-manifold topology from the native fine order topology on the surreal class. Their Lean scope is also delimited: the cited small-set closed/discrete and set-indexed-net statements do not formalize the whole added class-manifold or connectedness discussion. No topological structure on a nonstandard model of arithmetic is inferred from the word “Borel.”

**Nonstandard arithmetic, residue images and Hahn transfer.** The selected `discrete-initial-subgroups-and-omnific-normalization` spans 4577–4640, 4746–4803, 5236–5309, 5349–5408, 5522–5609 and 5650–5815 support the distinctions in the new `polish-models`, `omnific-diophantine-geometry` and `independent-surreal-copies` notes. The exact residue/profinite-image statements concern one standard-system oracle and are separated from the Borel properness argument. Equality of standard finite quotients or abstract completions does not identify the canonical images. The Borel-model application uses an explicitly imported Glazer standard-system fact; the target itself says its placement did not consult the underlying slides. That external premise is **not independently verified here**.

The Hahn independence transfer is over the specified restricted coefficient field. The coefficient-extension lemma at `independent-surreal-copies` 2894–2934 supplies the stated implication by coefficientwise linear disjointness, and multiplication by nonzero base-field units preserves independence. This does not establish independence over the full real coefficient field. The perfect/Cantor structure lies on real coefficients or their transported parameter space; the omnific image can be discrete in its native order topology, as 5790–5815 expressly explains.

**Countable surreal subfield coding.** The selected `cantor-families-of-surreal-subfields` spans 203–237, 430–499, 568–601, 683–713, 740–780, 860–930 and 1107–1170 support the reciprocal scope: a countable real-closed ambient field; a closed Cantor family in the subset-coding space; real-closure meet/join statements; and intrinsic valuation/rank/component constraints on ordered-field embeddings, not merely chosen-generator maps. These objects are distinct from the full Hahn fields and from inclusion-only Boolean-family statements in neighboring reports.

The fixed-field embedding locus is the complement of the well-order support locus. The comparison with `polish-models` 4535–4577 preserves quantification over subsets of one fixed countable order and its scattered/non-scattered dichotomy. It neither makes the decomposition computable nor answers the broader fixed-source question. “Complete analytic” here describes a descriptive-set-theoretic reduction; it supplies no fixed-arity Diophantine polynomial or paid arithmetic compiler.

**Radicals and formalization.** The support-coset lemma at `definable-surreals-and-omnific-integers` 1750–1786 matches the stated independence specialization. The `tail:lem:signs` source statement and the two named Lean declaration excerpts were read as text. Their hypotheses—independent square classes, characteristic different from two, distinct prime parameters and chosen square roots—fit the rational specialization. The guide correctly says that the specialization itself is not a separate Lean declaration and that the rest of the new countable-field report is not thereby formalized. No Lean execution or dependency/kernel audit was performed.

**Hat-game comparisons.** `measurable-box-games` 1283–1313 defines legality, fixed finite observations per player and the product topology; the finite bound can vary with the player. Its dominant-block category/success statements at 2020–2100 give the cited conull, meager, Σ⁰₂-complete success set for the constructed strategies. The new guides only identify a measure/category contrast and explicitly disclaim a shared theorem with open-query games or the non-Baire ideal construction. They do not assert that every finite-information strategy has this success set.

## Limits and execution record

Only fresh metadata scripts and read-only Git/text operations were executed. **No supplied, archived or frozen program was executed or imported; no copied predecessor program was executed. No Lean, LaTeX, PDF or manuscript build was run. No repository file or Git state was changed.**

Historical source pins, author priority, claims about the absence of other reports, external bibliography dates, and reported delivered build/test successes remain attributed manuscript statements. They are not independently certified by this review. Selected target readings test the new comparisons and their hypotheses; unread portions of the target manuscripts are not covered.

The complete byte/read-span evidence is `/tmp/review_batch90_reciprocal_e50dde15b.json`. The fresh recorder is `/tmp/review_batch90_reciprocal_e50dde15b_metadata.py`, using the prior fresh metadata inputs `/tmp/reciprocal_e50_inventory.json` and `/tmp/e50_target_index.json`; none is a mathematical theorem prover. This checkpoint establishes no new arithmetic bound or universal compiler.
