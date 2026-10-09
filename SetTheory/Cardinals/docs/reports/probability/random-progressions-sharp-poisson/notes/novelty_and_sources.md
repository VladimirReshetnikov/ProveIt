# Literature comparison, provenance, and priority status

## Narrow contribution proposed for review

The proposed research contribution is the combination of an explicitly
computed entropy coefficient, an O(n^-1 log^(3/2)(n)) uniformly corrected
avoidance law, sharpness of the uncorrected n^-1 log^2(n) error, and its
lattice-periodic leading coefficient with explicit liminf and limsup.
These formulas were derived for this manuscript. Independent mathematical
review and a wider literature search are still required before claiming
priority or describing the work as an established breakthrough.

The search and review were focused, not exhaustive. No claim is made that
the displayed comparison is the latest bound in all published or
unpublished literature. Some broad web searches were noisy and did not
resolve priority. Absence of a matching result in the few inspected
sources is not evidence of worldwide novelty.

## Primary literature actually used

1. Itai Benjamini, Ariel Yadin, Ofer Zeitouni, *Maximal Arithmetic
   Progressions in Random Subsets*, ECP 12 (2007), 365--376.
   Corrected preprint v2: <https://arxiv.org/abs/0707.3888>.
   Used for historical context concerning longest progressions and Poisson
   methods. The manuscript does not repeat the abstract's centering formula.
2. MinZhi Zhao, Huizeng Zhang, *On the longest length of arithmetic
   progressions*, arXiv:1204.1149 (2012).
   <https://arxiv.org/pdf/1204.1149>.
   The inspected PDF's printed page 3 gives Theorem 1.1(1), equation (1.5):
   a uniform O(n^-1 log^4(n) log log(n)) approximation using the smooth
   parameter. Printed pages 8--11 give the progression-head reduction and
   Lemmas 3.1--3.2. The theorem page and the overlap proof pages were also
   inspected as rendered page images.
3. Frank Mousset, Andreas Noever, Konstantinos Panagiotou, Wojciech Samotij,
   *On the probability of nonexistence in binomial subsets*,
   <https://arxiv.org/abs/1711.06216> and
   <https://arxiv.org/html/1711.06216v2>.
   Used to distinguish the existing general cumulant/nonexistence framework
   and fixed-length AP applications from the growing-length calculation
   here. The local nonmonotone avoidance proposition in the manuscript is
   proved in full and is not an unverified invocation of that paper.

## Repository context inspected

- <https://github.com/VladimirReshetnikov/ProveIt/tree/main/Combinatorics/Ramsey>.
  The Ramsey `Research` directory listed GowersSzemeredi,
  QuasipolynomialProgressions, SquareDifferences, and VanDerWaerden.
  The returned tree identifier was
  `feed930818b6ef23ee52b786139afda86e80ca01`.
  `RandomProgressions/SharpPoisson` is a proposed new destination, not a
  claim that the directory was already present.
- <https://github.com/openai/math>.
  README/catalogue context and the directory/citation metadata for
  *Quasipolynomial Bounds for Arithmetic Progressions* (September 23, 2026)
  were inspected. The latter README blob identifier returned by GitHub was
  `157e5c6a2f863adc4b99380fd1755a1f5af24695`.
  The repository explicitly describes mixed verification status. No
  mathematical assertion of that manuscript is used as a premise here.

Inspection date: October 7, 2026 (request date). The identifiers above are
specific returned tree/blob identifiers, not claimed full-repository
commit pins.

## Inherited ingredients versus proposed refinements

The head/declumping construction, smooth parameter, and pair-overlap bound
are existing ingredients. Their proofs are included for a self-contained
dependency chain, not to claim their invention. The second-factorial-
cumulant principle is also established methodology. The general local
lemma in Section 3 is packaged and proved for this argument; its abstract
priority has not been investigated exhaustively.

The manuscript's strongest distinctive calculations are the squared
entropy degree profile in the growing-length problem, its conversion into
a signed covariance coefficient, the weighted remainder sufficient for a
uniform correction, and the explicit sharp lattice-error calculation.
