# Harmonic Parity and Resolvent Identities

**Research continuation for ProveIt — 11 October 2026**

This package contains a comprehensive article, complete TeX sources, analytic
proofs, exact symbolic verification programs, independent numerical diagnostics,
and source and integration metadata.

The inspected source baseline is commit
**c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4** of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4).
The baseline includes nine incoming archives. Their exact hashes and the
selected canonical source hashes are recorded in provenance/SOURCE_SNAPSHOT.json.

## Read the article

- [Harmonic_Parity_and_Resolvent_Identities.pdf](Harmonic_Parity_and_Resolvent_Identities.pdf)
  is the complete rendered article.
- [Harmonic_Parity_and_Resolvent_Identities.tex](Harmonic_Parity_and_Resolvent_Identities.tex)
  is the complete standalone source, including the bibliography.
- article.tex, preamble.tex, references.tex, and sections/ contain the editable
  modular version.
- [integration/INTEGRATION.md](integration/INTEGRATION.md) proposes placement in
  the repository and records the definitions and qualifications to preserve.
- [integration/CLAIM_LEDGER.json](integration/CLAIM_LEDGER.json) gives exact
  theorem labels and separates new developments, inherited statements,
  normalized restatements, and unresolved questions.

## Main proved contributions

### 1. Exact centered harmonic cancellation

For a polynomial P in generalized harmonic numbers, the Dirichlet series

$$
\mathcal D_P(s,\tfrac12)
=\sum_{n\ge0}\frac{P(H_n,H_n^{(2)},\ldots,H_n^{(R)})}{(n+\tfrac12)^s}
$$

is regular at every nonpositive even integer if and only if P is invariant
under the simultaneous transformation

$$
X_{2j}\longmapsto 2\zeta(2j)-X_{2j},
\qquad X_1,X_3,X_5,\ldots\longmapsto X_1,X_3,X_5,\ldots.
$$

This resolves Q11 of the pinned Exact Resonant report. Sufficiency follows
from centered Bernoulli parity. Necessity is proved using the formal Laurent
case of the Adamczewski–Dreyfus–Hardouin difference-equation theorem, after
proving that the relevant formal trigamma series is not rational.

The assertion is about functions and formal expansions. It does not assume
arithmetic independence of Euler's constant or zeta values. The complete
principal-part formula at arbitrary positive shift is also included.

### 2. All centered trigamma-square moments

Every even centered continued value of

$$
\mathcal T(s)=\sum_{n\ge0}\frac{\psi'(n+1)^2}{(n+\tfrac12)^s}
$$

is given by a finite Bernoulli formula in the two-dimensional space
Q + Q zeta(3). After explicit polynomial subtraction, the identities are
ordinary absolutely convergent sums. For example,

$$
\sum_{n\ge0}\left((n+\tfrac12)^2\psi'(n+1)^2-1\right)
=-\frac14\zeta(3)-\frac16.
$$

The entire sequence is summed by a convergent exponential generator involving
Li_2(exp(-t)), Li_3(exp(-t)), and Li_4(exp(-t)). The proof uses finite summation
by parts and exact constant-term extraction. It is distinct from the source's
weighted squares of differences of shifted trigamma functions.

### 3. Completed rational cotangent transforms

Put K(x) = pi cot(pi x) and R_z(x) = 1/(K(x)-z), with z nonreal. The article
evaluates every coordinate finite part

$$
\operatorname{FP}_x\int_0^1\gamma_m^{(p)}(x)R_z(x)\,dx
$$

in finitely many ordinary polylogarithmic order derivatives. The full contact
polynomial is retained before spectral coefficient extraction. Repeated
resolvents follow by z derivatives, and partial fractions give every rational
function of K bounded at infinity and without real poles.

At the first nontrivial derivative,

$$
\operatorname{FP}_x\int_0^1
\frac{\psi'(x)}{\pi\cot(\pi x)-i\pi}\,dx
=1-\gamma-\log(2\pi)+\frac{i\pi}{2}.
$$

The constant 1 is an endpoint contribution. The article also evaluates the
transform of the established Espinosa–Moll generalized polygamma function at
continuous order, proves its exact integer-order conversion, and gives every
balanced Gamma primitive. All branches and finite-part coordinates are stated.

### 4. Arbitrary-depth harmonic deletion and an analytic Lerch generator

A fixed nonpositive index can be removed at any position in the entire relative
harmonic interpolant. The proof works at arbitrary endpoints, directly with
ordered Hurwitz identities and deconcatenation. It does not infer holomorphic
uniqueness from integer endpoint differences.

The resulting canonical finite normal form has explicit polynomial endpoint
coefficients and a proved total degree budget. Every word with one surviving
free order reduces to finitely many ordinary Hurwitz-zeta differences, including
all derivatives in that free order.

Arbitrarily many zero indices before and after one free order are summed in a
convergent Lerch generating function. Its combined branch cancellation and
entire spectral continuation follow from an explicit normalized Mellin kernel.

The fully indexed polynomial Stieltjes primitive formula is classified as an
arbitrary-endpoint extension and restatement of the classical mechanism already
present in the canonical manuscript. It is not counted as a new integration
principle.

### 5. Every quartic Tornheim ray and the formal higher-order kernel

Using the inherited holomorphic remainder R, every admissible fourth directional
derivative of T(A,B,C) reduces to three coordinates:

$$
\Lambda=\left.\frac{d^4}{dt^4}T(t,t,t)\right|_{t=0},
\qquad U=R_{AAA}(0),\qquad \Xi=R_{AAB}(0).
$$

The coordinate U is a specialization of the source's convergent Gamma series.
The mixed coordinate Xi receives an ordinary absolutely convergent integral
of polylogarithmic order derivatives, with explicit subtractions and constants.

Cyclic quartic combinations cancel U and Xi. For instance,

$$
W_{1,2,3}^{(4)}(0)+W_{2,3,1}^{(4)}(0)+W_{3,1,2}^{(4)}(0)-36\Lambda
=-184\log(2\pi)\zeta'''(0)+156\zeta''(0)^2-386\zeta''''(0).
$$

At every remainder degree d, the article determines the exact formal freedom
under the stated symmetry, axis, and Euler-plane constraints. Its dimension
for d at least 2 is floor(d/2) + floor(d^2/4). The cyclic image is exactly ABC
times the symmetric homogeneous polynomials of degree d-2. An explicit
deformation preserves the diagonal and the named relations while changing
the cyclic fifth layer.

These counts concern the specified formal relation system. They do not assert
arithmetic independence or impose every possible Tornheim relation.

## What remains open

The short S6 reduction and the revised S8 reduction remain conjectural. The
older rejected S8 vector is a separate candidate. Existing bounded
relation-space obstructions are not period nonvanishing theorems.

The article does not reduce Lambda or Xi to a finite algebra of standard
constants. It does not evaluate every positive-index harmonic Stieltjes
coordinate or every unbalanced Barnes product.

Section 9 gives thirteen concrete research questions, including mixed
harmonic-tail moments, shifts other than one half, cancellation of global
spectral remainders, complex-power cotangent kernels, multivariate Lerch
generators, transverse derivatives at deleted harmonic indices, additional
Tornheim functional relations, and a functional bridge to the actual Gaussian
conjectures.

## Rebuild the PDF

A standard LaTeX installation with pdfLaTeX and the packages named in
preamble.tex is sufficient. No network access is required.

    python3 build.py

This regenerates the standalone source and makes three pdfLaTeX passes.
The generated auxiliary files are confined to build/.

To regenerate only the standalone TeX:

    python3 build.py --no-pdf

The standalone file can also be compiled directly:

    pdflatex Harmonic_Parity_and_Resolvent_Identities.tex
    pdflatex Harmonic_Parity_and_Resolvent_Identities.tex
    pdflatex Harmonic_Parity_and_Resolvent_Identities.tex

## Reproduce the mathematical checks

Python 3.10 or later, mpmath, and SymPy are required. The actual versions used
are recorded in results/environment.json. The requirements file gives
compatible dependency ranges.

Routine exact and moderate numerical checks:

    python3 code/verify_all.py

Full independent comparisons, including the slower direct Stieltjes and
Lerch evaluations and the Tornheim Mellin checks:

    python3 code/verify_all.py --full

The runner writes fresh results into results/latest/ and preserves the
original full records delivered at the top level of results/. Individual
scripts can be run separately:

    python3 code/verify_harmonic.py --exact-only
    python3 code/verify_harmonic.py
    python3 code/check_quartic_tornheim.py --numeric
    python3 code/verify_resolvent.py --full --progress
    python3 code/verify_harmonic_parity.py
    python3 code/verify_resolvent_contact.py

The independent checks cover symbolic normal forms and principal
coefficients, finite nested sums, noninteger endpoint continuation, ordinary
and finite-part quadratures, continuous polygamma orders, Gamma primitives,
and asymmetric Tornheim rays. The proofs do not depend on numerical
recognition or integer-relation searches.

### Interpretation of the records

- Exact symbolic checks are finite algebraic checks over the specified
  coefficient rings.
- Floating-point comparisons are diagnostics, not interval certificates.
- The analytic theorems are proved in the article; they have not been
  verified by a proof assistant.
- Review notes record independent mathematical derivations and visual
  inspection. They are not external peer review.
- Two numerical implementation issues caught during checking were corrected
  without changing a theorem or relaxing a tolerance. The records and article
  explain the arbitrary-precision reciprocal and native Hurwitz derivative
  fixes.

## Package structure

| Path | Purpose |
|---|---|
| Harmonic_Parity_and_Resolvent_Identities.pdf | Complete article |
| Harmonic_Parity_and_Resolvent_Identities.tex | Complete standalone TeX |
| article.tex, preamble.tex, references.tex, sections/ | Modular editable source |
| build.py | Standalone generation and PDF build |
| code/ | Exact reduction and verification programs |
| results/ | Actual completed exact and numerical records |
| integration/ | Proposed placement and claim ledger |
| provenance/ | Source hashes and independent review records |
| requirements.txt | Python dependency ranges |
| SHA256SUMS | Checksums of delivered package files |

The package is an AI-assisted analytic research contribution prepared for
review and integration. No authorship assignment to the repository owner is
made. Mathematical developments are claimed relative to the inspected
repository baseline; no literature-wide priority claim is made.
