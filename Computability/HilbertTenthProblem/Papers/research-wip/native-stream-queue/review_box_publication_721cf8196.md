# Bounded publication review: measurable-box-games Parts III–IV

**Two corrections requested:** the new Q9 status overstates which cases remain open, and one indicator-macro rename was missed. No defect was found in the inspected adaptive-extension and deterministic expected-query proof chains. This is a scoped mathematical/publication review, not certification of every proof in the 5,570-line TeX change. No paid Diophantine compiler improvement follows.

## Immutable evidence and exact scope

Commit `721cf81969897cecd69d9fe2ae757ad12dffd511`, parent `47a77dabab8e3eb9f8df7400315692324d9e8a24`, changes only these files under `SetTheory/Cardinals/docs/reports/ordinals-and-order-types/measurable-box-games/`:

| File | Bytes | SHA-256 | Read scope |
|---|---:|---|---|
| README.md | 76,812 | `03c6b2b94da24b8672f557452ae9e62b93a502faa1eb5f4325a30172469bde51` | Complete 785-line raw diff, including all additions/removals and displayed context |
| article.tex | 490,336 | `40c42e3c06dd5b5e755a15de71d78fe350170ff6de414df32c3348208c3b2cdc` | 2,375 conservatively recorded lines in the exact spans below; headings scanned throughout; full source text compared mechanically |
| article.pdf | 1,329,011 | `26321cae4c482ade37e3233910d630604835e07738813aa91ada88c1bec517da` | Hash only; no rendering or build |

Recorded TeX reads: 1–110, 202–245, 1014–1068, 2809–3228, 3373–3634, 3760–3786, 4030–4065, 4095–4169, 4239–4350, 4686–4882, 4934–5000, 5085–5135, 5184–5254, 5377–5582, 5880–6040, 6170–6228, 6246–6375, 6380–6458, 6690–6725, 7200–7224, 7358–7449, 7450–7484, and 7700–7724. Each span has its own byte hash in the JSON. Other displayed/header scans are not promoted to a complete proof read.

The prior `review_hat_threshold_afd7ffabb.md` and `review_hat_placement_e38f368c2.md` were read fully as inert evidence. The former's substantive proof scope remains its original source lines 216–578, 795–1380 and 1466–1663; the latter was byte-placement evidence only, before the Parts were integrated. This review neither silently widens their scope nor reruns their helpers.

No applicable `AGENTS.md` lies on this host's ancestor path. The incoming standing rule at lines 426–440 was applied: incorrect or unproved claims are retained with attribution and explanation. No repository edits or Git mutations occurred. No supplied, archived, frozen or copied predecessor program was executed/imported; no builder or proof assistant ran. Only fresh metadata/text-comparison code ran.

## Findings

### B1 — the revised Q9 open-range sentence is still false

Immutable README lines 348–350 say:

> Still open: `q = 2` outside these families, every `q ≥ 3` with
> `⌊m/q⌋ < t ≤ m`, and the first parameters at which the legal and blind optima
> differ (in every settled case they coincide).

The new article line 1053 similarly says: “Open are the remaining parameters, in particular $q=2$ outside these families and every $q\ge3$ with $\floor{m/q}<t\le m$”. These are newly added status claims, not the preserved batch-90 sentence that Remark 15.1 already refutes.

A counterexample is `(m,q,n,t)=(1,3,1,1)`: the legal and blind optima are both `1/3`. The player makes a constant guess at the sole box without inspecting it.

More generally, for every finite `n≥1`, `q≥2`, `m≥1`, and positive integer `t` dividing `m` with `⌊m/q⌋<t≤m`, both optima are exactly `m/(qt)`. To prove the upper bound, partition each blind output by its target `i` and predicted color `a`. Every such fibre is invariant under changing coordinate `i`; exactly one of its `q` equally likely values is correct. Hence each player's success probability is `1/q`, so `E S=m/q` and Markov gives `P(S≥t)≤m/(qt)`. For attainment, put `k=m/t<q`, choose `k` distinct colors at one shared fixed box, and assign exactly `t` constant guesses to each color. This zero-query legal team scores `t` on those `k` colors and zero otherwise. Its probability is `k/q=m/(qt)`.

Shared targets and constant guesses are explicitly permitted by Part I's model (article 202–241), its minimax construction, and the new Remark 15.1(a). In particular `t=m` gives optimum `1/q` for **every** `n≥1`; this also supplies cases with fewer boxes than the own-hat constructions require. This argument does not modify source 04's different, fixed-own-hat, minimum-depth theorem.

The precise README/TeX replacements and a suggested new numbered Remark 15.2 appear in `/tmp/box_publication_721cf8196_proposed_edits.md`. They preserve the wrong batch-92 phrase with the counterexample, add the divisor family, and replace the exhaustive openness claim by the narrower statement that the general remaining optimization and first legal/blind separation are unclassified by this report.

### B2 — one unbraced indicator argument escaped renaming

Article line 7210, Theorem 65.3, still reads `For $f=\ind C$`. In the original `hat_inspection_frontier.tex` line 1576, this works because its `\ind` macro takes one argument. The merged host's `\ind` takes **no** argument; the write introduced `\indic` for source 04's one-argument indicator. Thus this occurrence now prints a product-like `1 C` rather than the indicator of `C`.

Replace it by `For $f=\indic{C}$`. The immediately following proof uses `F=d-2sf`, confirming the intended indicator. This was the only labeled-statement mismatch after the declared renames, and the only unbraced `\ind C` occurrence found. Preserve the original bytes in this review; the mathematical statement itself needs no new proof.

## Publication/source authentication

All 23 regular members of the three immutable arrival archives were freshly hashed. All 13 ancillary files placed at `e38f368c2` still equal their archive members byte for byte and are unchanged by this publication. The manifest identifies every member, placed path, hash and coverage:

| Archive | Arrival | SHA-256 |
|---|---|---|
| adaptive_box_games_research.zip | `9dc8db274` | `e8032c15ea71c4f8a6de0b9efe753ec94b5a3ccfa3b21fb655c37cac0a7c0a01` |
| hat_inspection_frontier.zip | `9dc8db274` | `85901802d4fe34d4d72fcff9db25e29b5d3ce67d908ffd890b335d81b44effae` |
| hat_query_thresholds_package.zip | `afd7ffabb` | `64e26f23af6e9bb850d4e5a1cf82ee2ebc1fbab2a33e12b76c15a9191effe3d4` |

Fresh ordered paragraph comparison uses the actual published portion for each source, whitespace normalization and the disclosed label/citation/macro/role renames, appendix/proof-heading adapters, and documented comma correction. All 168 scientific-body paragraphs of source 03 and all 178 of source 06 are present in order. Of source 04's 203, 199 match; three unmatched paragraphs are exactly its two replaced path/block proofs, whose explanatory pointers retain their content, and the fourth contains B2. All three abstracts match after these transformations. This is preservation evidence, not a proof audit of every matched paragraph.

Of 82 labeled statement blocks, 81 match exactly after the declared transformations; B2 is the sole discrepancy. All 126 prior labels survive, all 199 delivered labels are present with their intended prefixes, and nine editorial labels give 334 unique labels. All 823 `ref`/`eqref`/`pageref` occurrences resolve. All 146 citation occurrences resolve to 35 bibliography keys; the original 13-key order is unchanged. Merged bibliography prose, external URLs, rendered label numbers and the claimed 143-page PDF were not independently certified.

## Mathematical and computational boundaries

**Part III.** The inspected finite classification correctly uses completed-base-measurable outputs into a standard Borel label space, rather than assuming random-coordinate evaluation is measurable. The invariant countable-support good set and diffuse-target escape lemma justify changing selected external coordinates while preserving a prescribed base event. Shared targets receive one common color; independent colors per player would be wrong. The finite density classification checks Radon–Nikodym necessity, representation independence and countable additivity. The countable kernel proof constructs cylinder densities and a measurable realization rather than assuming the uncountable base admits ordinary disintegration. Its preservation of the completed base uses a fresh countable support for each event.

The Borel/universal minimax conclusion is appropriately separated from the unresolved Baire-property clause, unrestricted ZF strategies, legal finite-query execution and almost-sure own-hat results. A fair measure extension does not find a losing configuration algorithmically or make a nonmeasurable success event canonically probabilistic. No new issue was found in these inspected arguments. The joint-law polytope and nonuniform-color proofs were not fully reviewed.

**Part IV.** The inspected deterministic lower bound properly uses feasible path probabilities, including repeated queries and almost-surely halting trees. A uniform expected cap below two forces a common finite depth bound. Finite coloring then excludes divergence without asserting independent scores or treating divergence as a tail event. The positive construction has finite individual trees, geometric query tails and means below two, with their **supremum** equal to two. Rare bad blocks are summable and independent gains occur infinitely often; the pair-prefix bound promotes endpoint growth to every prefix. The general nondecreasing-cost lower bound first takes sufficiently deep players and then monotone limits; it does not interchange a supremum with an infinite sum.

The count-budget theorem retains eventual positivity, while count and distance remain different resources. Free public/private coins change the model and are expressly separated. The computed schedule and infinite probability-one event do not supply a bounded-time certificate. The published threshold is therefore not “two queries on every run” or a two-operation arithmetic circuit.

The full source-04 Fourier/affine minimum-depth necessity proof, covariance/variance and strong-law chain, CLT and realized-cost limit were not freshly certified here. Their statements were authenticated against the source and their domain boundaries inspected. The source-06 sparse-support refinements and externally cited sharper analytic constant also remain outside this proof review. Historical execution totals, package tests and novelty claims are source assertions, not new reviewer runs.

Finally, the proposed list-coding/reflection developments remain proposals. Neither measure extensions, Boolean degree, expected observation count nor an infinite success event supplies a complete paid fixed-arity ordinary-integer polynomial compiler. No universal arithmetic gate or witness bound changes.

## Frozen artifacts

- Manifest: `/tmp/review_box_publication_721cf8196.json`, SHA-256 `f550042b476a0f576e0874c8f3124a83ecd18bda4951950ff0d6ce52e0775deb`.
- Exact proposed corrections: `/tmp/box_publication_721cf8196_proposed_edits.md`, SHA-256 `924dba23ac4c8e61213e26233714e01473fb45b2e3d0a01107b8493ac5f73c88`.

These artifacts assess immutable `721cf8196`; any later repair is a separate revision and does not erase the two findings above.
