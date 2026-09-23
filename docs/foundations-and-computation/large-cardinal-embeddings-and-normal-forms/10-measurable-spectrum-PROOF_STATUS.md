# Proof status and review priorities

## What the delivery establishes and what it does not certify

All numbered mathematical claims in the article have written proofs or are explicitly marked as imported constructions with their dependencies stated. This is not independent referee review or a Lean formalization. The finite program verifies no infinite or large-cardinal assertion. Candidate novelty is separate from the correctness of the displayed proofs.

## Claim inventory

| Result | Main assumptions | Proof route and status |
|---|---|---|
| Lemma 3.1: countable detection of Hahn summability | Set-indexed families, well-ordered set supports, choice | A failure of local finiteness or of well-ordering has a countable witness; elementary argument supplied. |
| Theorem 4.2: finite complete-ultrafilter representation | Real or complex scalars; preservation of point-finite sums of size below an uncountable theta, including finiteness of nonzero scalar images | Specialized null-ideal proof of a classical product-map mechanism credited to Bergman; not claimed as a new general factorization theorem. |
| Lemma 4.4: first incomplete partition | Countably complete nonprincipal ultrafilter | Least small-set partition and pushforward give a measurable cardinal; classical argument supplied. |
| Theorem 5.1: least failure is measurable | Coefficient-linear map between full real/complex Hahn fields; every countable Hahn sum preserved | Localize one defect to one support product and output coefficient; use Theorem 4.2 and Lemma 4.4. Proposed Hahn/surreal contribution. |
| Theorem 6.1: canonical strong part | Same countable strongness and coefficient linearity | Monomial images are summable; a locally finite double-family argument constructs the unique strong extension. Proposed general package. |
| Theorem 6.3: finite algebra of the strong part | Countably strong coefficient-fixing field embedding, or coefficient-linear derivation | Regroup summable products of monomial images. Written proof supplied. |
| Theorem 7.2: ordered additive transvections | A measurable kappa; a nonprincipal kappa-complete ultrafilter on kappa | Explicit coefficient evaluation on a bounded negative support and a rank-one square-zero operator. Group law, order, leading terms, Oz preservation, exact first failure, and nonmultiplicativity are proved. |
| Theorem 7.4: parameter avoidance | A set of surreal parameters | Put the detector support strictly below the union of their supports. No class basis or proper-class Zorn argument. |
| Theorems 8.1 and 8.2: support criterion and sharp size | Full set-sized Hahn field; real/complex scalars | Product localization and binary support masks; attainment in the rational span of the detector exponents. Real closedness uses the classical Hahn-field theorem. |
| Theorem 9.1: surcomplex transfer | Complex coefficient linearity; measurable cardinal for the converse | Apply the scalar evaluation argument to real and imaginary coordinates. Conjugation compatibility requires real transvection parameter. |
| Proposition 10.1: elementary-embedding construction | Measurable cardinal, normal ultrapower | Existing repository construction, not a new result here. Imports sign-code arithmetic and normal-form absoluteness from the critical-point report. |
| Theorem 10.2: exact boundary for countably strong field embeddings | Same foundational conventions; coefficient-fixing and Oz preservation | New lower bound plus imported Proposition 10.1. Does not concern arbitrary nonstrong embeddings without the countable hypothesis. |
| Theorem 10.4: unrepresentable target test | The measurable-cardinal embedding J of Proposition 10.1 | Missing exponent kappa gives a pulled-back coefficient functional zero on all monomials but nonzero on an explicit sum. Conditional consequence; not a counterexample among strong field embeddings. |

## Highest-value independent review tasks

1. Review the support-null ideal proof, especially its closure under fewer than theta unions, the finite Boolean quotient, and the uniqueness of its ultrafilter factors. The word “sum” in the scalar target always means a finite nonzero family.
2. Review the localization of a least failing family and the distinction between preservation of admissibility and preservation of its value. Countability already gives admissibility for every set-indexed family.
3. Review the exponent convention: `t^g = omega^(-g)`. The detector exponents `s_alpha = d - omega^(-alpha)` increase and form a well-ordered set; a reversed convention would invalidate the construction.
4. Check the transvection support separation: detector support lies in `[d-1,d)`, correction at `d`, and the product test lies in `[2d-1,2d)`, for `d <= -1`.
5. Review the existing critical-point report's normal-form absoluteness independently before treating Section 10 as independently established. The earlier sections are independent of this import.

## Foundational boundaries

Set-sized statements use ZFC. Class statements use NBG with global choice and individual class functions; all supports, products used for localization, and summation families remain sets. Assertions over all class maps are class-quantified statements, not constructions of a class of proper-class maps.

Measurability means an uncountable cardinal carrying a nonprincipal kappa-complete ultrafilter. The lower-bound theorem produces such a cardinal in the ambient universe; it does not only produce one in an inner model. No new consistency result is claimed.

## Deliberate nonclaims

- No proof that every nonstrong omnific-preserving field embedding requires a measurable cardinal: an embedding failing countable sums is outside the theorem.
- No unrestricted valuation-preservation theorem for Gaussian-omnific ring automorphisms.
- No target-test theorem for all strong proper field embeddings.
- No classification of arbitrary support-restricted Hahn subfields.
- No automatic assembly of arbitrary local ultrafilter matrices into a global Hahn map.
- No assertion that the additive examples preserve multiplication, the omega-map as a function, the Gonshor exponential, or the Berarducci–Mantova derivation.
- Fixing every monomial as an element is not compatibility with the omega-map as a function on moved exponents.
- No global entire-series representation; the additive examples are locally translations on infinitesimal neighborhoods.
- No claim that a set-sized canonical omnific-type ring has the entire Hahn field as its fraction field.

## Finite verification

The delivered program passed 11,955 exact rational assertions in 18 categories. Its finite functional is a principal coefficient projection. It does **not** simulate a nonprincipal ultrafilter and does **not** fix every monomial. The tests only check the algebraic nilpotence, transvection group laws, inverses, order/leading-term/constant-term preservation, finite omnific-type membership, weighted-coordinate identities, and nonmultiplicativity formulas.
