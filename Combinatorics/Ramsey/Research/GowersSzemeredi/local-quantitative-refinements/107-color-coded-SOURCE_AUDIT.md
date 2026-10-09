# Source and provenance audit

Review date: October 7, 2026 (America/Los_Angeles). The purpose of the repository review was to locate a concrete asymptotic problem and distinguish predecessor results from the new construction. This is not an audit of either entire repository.

## ProveIt

Repository: https://github.com/VladimirReshetnikov/ProveIt

The root README was read. The relevant public integration note was read in full:

`Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/106-torus-defect-INTEGRATION.md`

Its returned blob SHA was `7a96b46532dc93fa03cdeee7cc407ef1f74904f3`.

An explicit later read of `refs/heads/main` returned commit `579bea70c69ea045b779328bd1a6826773c74536`. Earlier search results used another indexed snapshot, `58175ca45563d9ee29875374dd77942f069268a9`. These should not be conflated: the branch changed or the search index was at a different snapshot. The integration-note blob hash is the specific content identifier used here. No repository write was performed.

### Predecessor manuscripts inspected in the user Library

1. **Torus Defects and Sharp Affine Partition Laws**, dated October 7, 2026. Library snapshots: `article(20261007-212040).pdf` and `article(20261007-212042).tex`. The first 90 source lines, the abstract/introductory search results, and the contiguous technical range at original source lines 170–819 were inspected. This includes torus capacity, equality/defect methods, the old support-layer construction, fixed-product asymptotics, and the regularized lower bound.

2. **Sharp Affine Localization for Quadratic Phases**, dated October 7, 2026. Library snapshots: `article(20261007-202938).pdf` and `article(20261007-202942).tex`. The first 70 source lines, including the title and abstract, and relevant indexed result statements were inspected; this delivery did not audit its full proof text.

No stable public path for these complete manuscript sources was established. The Library content was used to identify the predecessor baseline, not to substitute for a proof in the present article. All predecessor estimates used in a proof here are reproved.

Predecessor results not counted as new: orthant containment, torus capacity, the point–torus defect, the Jensen lower bound, existence of the regularized rate, old U_{s,m} constructions, the fixed-s/fixed-m large-q asymptotic laws, and the old two-cross exact values.

## openai/math

Repository: https://github.com/openai/math

The README was read. Its returned blob SHA was `8ac0cb7dbf1f38ad3b7480310d4e1d9482f0cfe8`. Search results used indexed commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The reviewed family metadata was:

- `preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/README.md`, blob SHA `157e5c6a2f863adc4b99380fd1755a1f5af24695`.
- `lean/docs/159.md`, blob SHA `66ef29e1f3a887a47889812669e9b736c4294b94`.

The latter scopes the selected formalized statement to the reciprocal-sum consequence and explicitly puts the paper's quantitative progression-free-set bound outside that statement. This is a distinction in the repository documentation, not an independent audit of its Lean proofs.

No theorem from this family, and no other global conjecture claim from the repository, is a dependency of the present work. The complete arithmetic-progression preprint was not audited for this delivery.

## Primary literature

P. Hall, *On Representatives of Subsets*, Journal of the London Mathematical Society, s1-10(1) (1935), 26–30. Publication metadata checked at the publisher: https://doi.org/10.1112/jlms/s1-10.37.26.

N. Alon, R. Yuster, U. Zwick, *Color-coding*, Journal of the ACM 42(4) (1995), 844–856. The author-hosted revised manuscript was opened and its first page visually inspected: https://web.math.princeton.edu/~nalon/PDFS/col5.pdf. DOI metadata: https://doi.org/10.1145/210332.210337.

The classical matching and elementary perfect-hash ingredients are explicitly credited and reproved in the exact form used. The novel claim is not the invention of either ingredient, but their application with common multiplicative-invariant fibers and tail chains to attain the affine-partition bound.

## Priority and verification limits

A focused search for affine partitions of coordinate crosses and related terminology did not establish prior publication of the new exact regions or high-arm constant. This is not an exhaustive literature or priority search. The phrase “proposed new theorem” in the status ledger means new relative to the inspected project baseline, with a proof supplied here, not independently validated world priority.
