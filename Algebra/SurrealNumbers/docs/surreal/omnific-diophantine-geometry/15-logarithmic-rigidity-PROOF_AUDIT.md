# Proof audit and verification boundary

This is an author-side audit of the arguments delivered with the article.
It is not an independent referee report and not machine verification.

## Sensitive steps checked in the mathematical argument

**Support condition versus valuation sign.** A consists of series with *all*
exponents nonpositive, not all series of nonpositive valuation. The latter set
would not provide the required ideal or zero intersection. The text gives an
explicit example distinguishing the two conditions.

**Arbitrary rank.** The characters are rational-linear functionals on the
rational hull of a set-sized ordered group. They need not preserve order. A
whole family, rather than one preferred derivation, separates nonconstant
series. Rational valuation inequalities are interpreted in the divisible hull;
Gamma itself need not be divisible or Archimedean.

**Strong sums.** The Euler derivation acts coefficientwise. Its Leibniz proof
uses finite convolution fibers, not interchange of topological limits. The
characteristic-two example explicitly distinguishes strong Hahn summation from
valuation-topological convergence.

**Elementary certificate.** The identity Uf+Vf'=1 produces
Dx/(m y^(m-1)) = (U(x)y/m)Dx + V(x)Dy. The right side is in I, while leading
valuations put the left side in V whenever m,deg(f)>=2. Zero derivative and
zero y are accounted for in the proof. The endpoint (2,2) needs nonnegative,
not strictly positive, valuation and is included.

**Properness.** The proper center is formed using Spec(V) and its fraction
field H. No equality Frac(A)=H is assumed. No map between Spec(A) and Spec(V)
is presumed; scalar contractions are compared at their common H-point.

**Logarithmic forms.** Local boundary coordinates have nonzero values at the
H-point, since it lies in the boundary complement. Their logarithmic
derivatives have nonnegative valuation. The entire spectrum of the local
valuation ring maps into a neighborhood of its closed-point image. This is
valid for arbitrary-rank, non-Noetherian valuation rings.

**Tangent vectors.** An Euler derivation need not preserve the function field
of the target image. Its restriction is a derivation into H. That is sufficient
for contraction with pulled-back differentials and for the one-dimensional
function-field argument.

**Smooth curves.** A nonconstant H-point of a curve over algebraically closed
k has generic image, so a nonzero rational differential remains a basis after
embedding the function field. Riemann--Roch supplies such a logarithmic form
except for P^1 with at most one puncture. Those exceptions are exhibited by
monomials when Gamma is nonzero.

**Semiabelian extensions.** The proof obtains the constant lift from ct(g),
not from an unjustified claim that G(k)->B(k) is onto. Non-split tori are
handled by an injective coefficient extension to a finite splitting field.

**Finite fibers.** A quasi-finite fiber over a field is a finite scheme.
Every image of its finite coordinate algebra in H is algebraic over k, hence
constant; nilpotents vanish in the domain. Positive-dimensional fibers are
explicitly excluded.

**Arithmetic descent.** Equality is reflected through an injective ring map
using the closed equalizer for a separated target. Faithful flatness of the
coefficient extension is not asserted or needed.

**Full surreal class.** Every point's finite presentation data are localized
in a set-sized exponent workspace. No proper-class spectrum or global choice
of a derivation on the full surreal class is used.

**Projective coordinates.** The tuple must generate the unit ideal. The proof
uses actual Bezout witnesses twice and the PID property of Z or Z[i]. It does
not replace unimodularity with lack of a common nonunit divisor, assume a GCD
theorem, or confuse affine integral points with projective rational points.

**Singular targets and normality.** The article does not assume A is normal.
It explicitly exhibits an element integral over A but not in A. Thus lifting
an A-point to a normalization is not an available unstated step.

## Computational and editorial checks

The exact finite checks in `code/verify.py` passed. They do not prove the
scheme-theoretic or infinite-support assertions. The PDF was compiled with
pdfLaTeX, rendered, and visually inspected, including the main certificate,
curve proof, and overall page layout. Final compilation has no LaTeX warnings
or overfull/underfull boxes.

## Remaining review tasks

Independent mathematical review should focus first on the functorial
contraction lemma and the passage from logarithmic annihilation to constancy,
then on the set-sized formulation of full-class arithmetic applications.
The elementary superelliptic proof is an independent, comparatively small
formalization target. Neither novelty priority nor independent proof checking
is supplied by this audit.
