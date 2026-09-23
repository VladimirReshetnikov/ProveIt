# Proof audit and boundary checklist

This is an author-side dependency check, not an independent referee report.
The mathematical proofs are in article.tex/article.pdf.

## Support and scalar equations

The field is the full Hahn field; a restricted series subfield is not silently
substituted. Exponents are well ordered in increasing t-notation.

The support lemma uses increasing forward orbits on theta(g)>g and increasing
inverse orbits on theta(g)<g. Well-ordering and finite fibers are separate
claims with separate proofs. The labeled version establishes strong additivity
for arbitrary summable input families. It is not inferred from convergence.

Both telescoping directions include the correct sign and scalar factors.
The finite tests retain endpoint terms; the infinite proof uses coefficientwise
cancellation in jointly summable families. Neither a cofinal orbit nor a
rank-one value group is assumed.

A homogeneous eigenvector on a moving orbit would force the entire bi-infinite
orbit into a well-ordered support. This excludes hidden kernel terms. On fixed
exponents the coefficient multiplier is exactly chi(g)-lambda.

The constant/resonance projection is linear but is not treated as a field
homomorphism on the whole field.

## Commuting actions and units

The exponent and character commutation identities are stated explicitly.
They make each resonance subset invariant under every other automorphism.
Uniqueness of normalized inverses then supplies commutation of all operators.

The homotopy identity uses exterior contraction anticommutators. The naive
coefficientwise wedge product is not claimed to turn the difference operator
into an ordinary derivation. Group cohomology is identified through the usual
finite free Koszul resolution of Z^d.

Infinitesimal logarithms use strong Neumann summability and characteristic zero.
The valuation-nondecreasing resolvent preserves the infinitesimal ideal.
Every multiplicative element is decomposed into valuation, leading coefficient,
and a principal-unit logarithm. A single exponent must solve the valuation and
character equations simultaneously. Compatibility by itself is not exactness.

## Definability and centralizers

The fixed field of a nonidentity rational dilation is exactly k. Surjectivity
of the difference operator onto zero-constant-coefficient series establishes
existence and uniqueness in the graph of the constant-coefficient function.

For doubling, comparing leading coefficients in D(x)=x^2 gives coefficient one.
Comparing the least positive correction exponent then eliminates every
nonmonomial factor. This proof does not assume a field order.

The geometric-series test distinguishes positive from negative monomial
exponents. The reciprocal of 1-m has constant coefficient 1 in the first case
and 0 in the second case. Monomial m=1 is excluded before division.

Every coefficient, rather than just the leading coefficient, is definable.
This is what proves that a commuting field automorphism must be strong;
strength is not assumed to prove the centralizer classification.

For rational q=a/b != 1, the power equation gives mu_|a-b|(k) times the
monomial group. Taking |a-b|-th powers recovers precisely the monomial group
because the exponent group is divisible. Distinct dilations are nevertheless
not conjugate, as their respective power-equation solution sets distinguish
an infinite set from a finite root-of-unity set.

## Arithmetic and proper classes

The Boolean-series sort contains exactly all subsets of N because every such
support exists in the full Hahn field. Field 1 represents natural-number 0;
the positive-exponent parameter m represents natural-number 1.

All admissible monomial parameters yield the same standard interpreted
structure. Explicit existential quantification over that parameter is used in
the undecidability reduction; undecidability of a reduct is not inferred solely
from naming an arbitrary parameter.

The TP2 witness has genuinely inconsistent rows and every transversal is
realized by a Hahn series with independently prescribed coefficients.

Ordinary cohomology and complete first-order theories are formulated for
set-sized structures. Full surreal conclusions are finite formula/equation
claims for set-supported normal forms and specified class automorphisms.
There is no claimed set of all class automorphisms or class cochains.

On No(i), recovering the complex coefficient field does not recover a chosen
real form. Arbitrary coefficient automorphisms of C remain in the centralizer.
A monomial dilation is not silently identified with a global exponential,
a derivation, or an exponential-preserving automorphism.

## Verification

verify.py checks 66,131 finite rational identities, including the exterior
algebra in dimensions 1 through 5. No infinite theorem or first-order semantic
statement is certified by this number. No Lean proof was produced or run.
