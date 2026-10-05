# Claim ledger

All general results below are proved in the manuscript in ordinary classical
mathematics. None is represented as independently reviewed or Lean-checked.
The finite test program is corroboration of algebraic identities only.

## Standing setting

Gamma is a nonzero countable divisible subgroup of ordered R. Coefficients
are real. Supports have finite intersection with every left half-line.
Borelness means the inherited coefficient standard Borel structure. A flow
is jointly Borel on R x L_Gamma and consists of unital field automorphisms.

## Claims and proof boundaries

| Claim | Location | Essential argument | Verification boundary |
|---|---|---|---|
| Connected Polish group actions on a countable-dimensional Borel-coded vector space have finite-dimensional cyclic orbit spans | Theorem 3.1 | Minimal-dimensional nonmeagre orbit preimage, Baire category, open stabilizer, connectedness | General proof only; not a new-priority claim for the underlying category principle |
| Borel field flows fix real coefficients and valuation | Section 4 | Scalar Borel Cauchy equation; order definable by squares; countable scaling image | Uses divisibility, real coefficients, and countable value group |
| Exact generator criterion and automatic entire coefficients | Theorem 5.2 | Window representations and compatible finite matrix exponentials; finite product-window argument | General proof only; no global Banach norm or formal summability assumed |
| Every Borel derivation is real-linear | Corollary 5.3 | Borel additive restriction to R and D(1)=0 | Does not assert arbitrary algebraic derivations are Borel |
| Strict integration iff window-local nilpotence iff iterate escape | Theorem 6.2 | Finite support in invariant cyclic spaces; filtration-tail argument | Strict increase alone is not escape |
| Universal strict integration iff finite rational rank | Theorem 7.2 | Minimum basis gain at finite rank; bounded independent chain at infinite rank | Constructed for every infinite-rank group in the stated setting |
| Complete finite-rank generator criterion | Corollary 7.3 | One common left-finite monoid of positive exponent shifts | Extends the strict case to zero-gain derivations |
| E and F integrate but E+F and [E,F] do not | Section 8 | Explicit rational-binomial shears; bounded successor chains | Sparse polynomial tests check finite identities, not the support proof |
| Product of two Borel time-one maps need not be time-one | Theorem 9.1 | Infinite independent integer orbit in a single window | Excludes every Borel flow, not just one logarithm construction |
| Exact and unique time-one embedding criterion | Theorem 9.5 | Positive triangular window spectra; canonical real powers; exponential-polynomial uniqueness | No claim for complex coefficients or arbitrary nonmeasurable actions |
| Tangent-to-identity local logarithm criterion | Corollary 9.6 | Local nilpotence and binomial/logarithm formulas | Formal sums controlled on each window, not by an assumed global gap |
| Complete finite-rank time-one criterion | Corollary 9.7 | Finite monomial basis images supply a common left-finite shift monoid | Borelness and valuation preservation retained |
| Strict integrability locus is Borel | Theorem 10.2 | Countable monomial/cutoff/iteration formula; Borel parameter evaluation | Not an algorithm or an optimized Borel-rank result |
| Surreal interpretation | Section 11.2 | Normal-form realization, or conditional transport along a specified embedding | Set-sized subfield only; no extension to all surreal numbers claimed |

The theorem numbers above are included for convenience; labels and titles
in the LaTeX source are the authoritative identifiers.

## Key checks against possible proof mistakes

1. The bounded exponent window is a countable-dimensional *direct sum*, not a
   finite-dimensional space and not a completed product.
2. Finite-dimensional orbit spaces are proved before coefficient derivatives
   are assembled into a left-finite series.
3. A product cutoff b for inputs with lower bounds a and c needs input
   cutoffs b-c and b-a, respectively.
4. In the general classification, coefficient sums may converge as real
   matrix-exponential series. In the strict case they are eventually finite.
5. A nonzero strictly increasing chain can stay bounded. The examples use
   rationally independent beta_n increasing to 2.
6. Shear group laws are proved on rational basis monomials and then extended
   using support control; merely specifying algebraic generator images is
   not treated as sufficient.
7. Time-one uniqueness uses real triangular spectra, so it does not import
   a false global complex logarithm inverse law.
8. The exact finite program does not use floating-point tests of rational
   independence, does not truncate a chain to zero, and does not assert a
   theorem from any fixed collection of samples.

## Unresolved matters

Independent proof review and priority determination remain open. The paper's
further questions concern effective recognition, joint BCH domains, exact
Borel complexity, zero-gain normal forms, nondivisible exponents, other
coefficient fields, larger support ideals, other parameter groups, and
foundational/formalization strength. No new Lean theorem is delivered.
