# Research status and provenance

## Exact selected question

Lucas Chiozini, Tamás Csernák, and Lajos Soukup, **Gamification of the T0-pseudoweight via cut-and-choose games on topological spaces**, arXiv:2510.05754v3.

- Version-specific source: https://arxiv.org/html/2510.05754v3
- Abstract and version history: https://arxiv.org/abs/2510.05754
- The abstract record retains the earlier title **Cut-and-choose games in topological spaces**.
- The version history retrieved for this report dates v3 to 29 May 2026.
- Source check: 19 September 2026.

Problem 1.3 asks whether the set-membership number of a topological sum is the supremum of the component values. Theorem 3.4 supplies an upper bound of that supremum followed by one additional move. The formal game definition permits an empty final intersection, which is winning for the Seeker.

The source question is answered negatively by the explicit convergent-sequence example in Section 2. No assumption of a precommitted hidden point, infinitude of a finite index set, or non-Hausdorff topology is needed. Countably infinite sums of the same sequence are counterexamples too.

A targeted literature search did not locate an intervening resolution. This records the search outcome, not a certified claim of first discovery. The article's counterexample and additional theorems are supplied with ordinary mathematical proofs for independent scrutiny; they have not been independently peer reviewed or formally verified in a proof assistant.

## Results established in the report

1. A two-copy counterexample, with component value 1 and sum value 2.
2. An exact finite decision-tree/alternating-closed-layer normal form.
3. Canonical oriented closure profiles and their componentwise sum rule.
4. An exact classification for all nonempty Hausdorff spaces of finite Cantor–Bendixson height.
5. Sharp one-extra-question examples at every positive finite level, using compact ordinal intervals.
6. Exact finite-product and bounded-height-sum formulae.
7. An omega-length upper bound for arbitrary sums of finite-membership-number components; equality for unbounded finite component values.
8. An exact classification on countable scattered Hausdorff spaces, including countable compact Hausdorff spaces and countable ordinal exponent intervals.
9. An alternating-chain formula and quadratic-time target algorithm on finite posets.

## Attribution of background machinery

The report does not claim to introduce Hausdorff difference hierarchies or canonical difference-chain methods. Relevant background includes:

Célia Borlido, Mai Gehrke, Andreas Krebs, Howard Straubing, **Difference hierarchies and duality with an application to formal languages**, Topology and its Applications 273 (2020), 106975.
https://arxiv.org/abs/1812.01921
https://doi.org/10.1016/j.topol.2019.106975

Borys Álvarez-Samaniego, Andrés Merino, **Some properties related to the Cantor–Bendixson derivative on a Polish space**, New Zealand Journal of Mathematics 50 (2020), 207–218.
https://arxiv.org/abs/2003.01512
https://doi.org/10.53733/82

All background lemmas needed for the principal classification are proved directly in the report. The third-party papers themselves are not bundled in this archive.

## Deliberate limits

The infinity symbol in the finite oriented profile means that no finite decomposition exists. It is not itself a transfinite difference rank. The report does not replace the finite ceiling logarithm by an ordinal logarithm and does not classify arbitrary uncountable-length games.

The original paper's questions about large countable point-separation ordinals and finite membership values on crowded spaces are separate from the question answered here. The constructed ordinal spaces are scattered and have isolated points.

The finite computations validate the finite-poset mechanism only. They do not constitute computer proofs of assertions about infinite ordinal spaces. Every infinite-space conclusion rests on the written argument.
