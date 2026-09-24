# Research and proof audit

## Repository comparison

Repository: VladimirReshetnikov/Surreal.
Pinned commit: `465a54b479a1ee842cbf7db1689a7d2f6bfe25e1`.

The GitHub connector was used to inspect the root README, repository tree,
docs catalogue, and the merged Hahn-valued measures report and its README.
The relevant comparison concerns that report's coefficientwise probability
sections, not its separate strong-additivity results.

Inspected points:

* Theorem 20.1 (`meas:thm:interior`) supplies the weighted square-summability
  criterion with a uniformly interior baseline for necessity.
* The proposition `meas:prop:general-l1` supplies absolute summability as a
  sufficient condition at arbitrary strictly interior baselines.
* Example 23.3 records failure of weighted-square necessity without uniform
  separation.
* Endpoint and mixed endpoint/interior results, countable-scale density
  theory, and the strong-measure classification already exist in the repo.

The proposed increment is the exact sum-space criterion at arbitrary
strictly interior baselines, its all-exponent lifting, and automatic
coefficientwise domination even when only a signed extension is assumed.
This audit is not a claim to have read every historical revision or every
unrelated repository proof.

## Published background and search scope

Relevant primary records checked include:

* Kakutani, *On equivalence of infinite product measures*, Annals of
  Mathematics 49 (1948), 214–224, DOI 10.2307/1969123. The publisher's
  archived issue table of contents confirms the bibliographic data.
* Neumann, *On ordered division rings*, Transactions of the AMS 66 (1949),
  202–252, DOI 10.1090/S0002-9947-1949-0032593-5; the Hahn support lemma is
  also explicitly recorded in the inspected repository's Hahn layer.
* Latała, *Estimation of moments of sums of independent real random
  variables*, Annals of Probability 25 (1997), 1502–1513. Used only for
  classical independent-sum context. The elementary Bernoulli proof does
  not depend on an unexamined general moment estimate.
* Bournez and Guilmant, *Surreal fields stable under exponential and
  logarithmic functions*, arXiv:2201.08199. Used for the established
  Hahn/normal-form viewpoint, not for the new measure criterion.

Searches included arbitrary/nonuniform Bernoulli products, total-variation
differentiability of infinite product measures, analytic complex product
measures, independent-series moments, and Hahn-valued probability. Some
publisher full-text endpoints were inaccessible. No exact published match
for the complete all-exponent theorem was identified in this bounded search.
That finding does not certify novelty, and the first-order split itself is
not claimed original.

## Proof review: delicate points checked

1. Uniform boundedness of first-order L1 norms is not mistaken for uniform
   integrability. An independent argument obtains the mixed sequence-space
   decomposition and hence actual L1 convergence.
2. Large symmetrized jumps use an event with exactly one selected large
   jump. Positivity of its infinite-product probability is proved after
   establishing summability of the selection probabilities.
3. A finite common coordinate split is proved for each finite group of rows;
   a separate arbitrary split for each row would not by itself justify the
   joint likelihood argument.
4. L1 limits are multiplied only across independent coordinate sigma-algebras.
   The proof does not assume that general L1 products are integrable.
5. Complex coefficient extraction is by Banach-valued Cauchy integrals from
   locally uniform L1 convergence. It is not pointwise substitution of a
   surreal number into an ordinary entire function.
6. The full Neumann lemma, including all word lengths, is used. No invalid
   Archimedean assertion that multiples of the least exponent are cofinal
   is invoked.
7. Necessity selects the least failed exponent. Its lower-order nonlinear
   remainder has already been shown to converge in L1, so it cannot cancel
   an unbounded first-order obstruction.
8. No domination, positivity, or prescribed coefficient support is assumed
   of a candidate signed extension. Uniqueness of finite coefficient
   measures derives these features afterwards where appropriate.
9. Uncountable exponent supports are handled coefficient by coefficient.
   No uncountable intersection of full-measure sets is used.
10. The imaginary-parameter test is restricted to real input rows. The
    analogous test at one fixed parameter is not asserted for arbitrary
    complex rows.
11. The scale map uses t^gamma -> omega^(-iota(gamma)), with the necessary
    minus sign and a specified additive order embedding.
12. Positive real event values are not confused with positivity of every
    coefficient measure, and coefficientwise addition is not confused with
    strong Hahn addition or fine-topological convergence.

## Delivered evidence and its limits

Full written proofs: in `article.tex` and `article.pdf`.
Finite exact verification: 4,670 rational assertions in `code/verify.py`.
PDF checks: successful compilation, settled labels, no overfull boxes,
page-boundary text check, rendered contact sheets and detailed page views.

There has been no external referee review, independent proof-assistant
verification, or certification of historical priority. The finite tests
are neither a proof of the infinite theorems nor a numerical decision
procedure for arbitrary input rows.
