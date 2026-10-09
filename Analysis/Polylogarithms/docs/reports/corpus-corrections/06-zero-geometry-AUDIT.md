# Scoped audit and proposed corrections

Target: `Analysis/Polylogarithms/docs/articles/stieltjes-parameter-derivative-tower.tex`

Repository commit: `c78c7c3dc2fc742a1af9492e47d578b3fb4e01e7`

Source blob: `e4d53b7c921c72ff40c5393a9d3ac5cfb44ea6bb`

Locations below use stable TeX labels and recognizable section titles. Approximate
source-line ranges refer to the inspected snapshot, not later revisions. These
are proposals; the original has not been modified.

## C1 — Unsupported independence conclusion (substantive logical correction)

**Location:** `sec:atoms`, “The new atoms are genuine,” near lines 310–325.

The section concludes that six second-order L/zeta derivatives are genuine,
mutually independent atoms after unsuccessful PSLQ searches at 200 digits.
A failed bounded numerical search cannot prove unrestricted rational linear
independence, algebraic independence, or irreducibility over a vocabulary.
An exact bounded-height exclusion would still be only a bounded exclusion.

**Proposed revision:** retitle the section “Unreduced second-derivative generators
and numerical searches.” Describe exactly what was searched (precision, basis,
coefficient-height limits, controls, and reproducibility data when available),
then say that no relation was found in those tests. Treat the six constants as
formal generators in that chosen representation, without an independence claim.
Do not invent a coefficient-height limit absent from the existing records.

## C2 — Universal rank statement lacks a printed general proof (proof gap)

**Location:** `thm:rank`, “k-independent rank,” near lines 199–214.

The statement asserts the formula phi(q)-1 for all q and k, but the accompanying
text reports exact row reductions only for q=3,...,30 and k=1,2,3. This is not
an induction, basis construction, or completeness proof. The distribution
relations have inhomogeneous known terms; the precise formal quotient should
be specified before assigning a residual dimension.

**Proposed revision:** separate the verified finite computation from the
conjectural general assertion unless a proof is supplied. Define the formal
ambient module and which inhomogeneous terms are treated as fixed. A correct
formal rank theorem would still not establish arithmetic independence of its
numerical special-value realizations.

This review supplies **no counterexample** and does **not** say the formula is
false. It identifies the gap between the printed evidence and its quantifiers.

## C3 — Trivial-zero normalization is underspecified (completion)

**Location:** `rem:parity`, following `thm:bridge`, near lines 275–288.

The text refers to a “first-nonzero-order variant” without specifying it. When
L(-k,chi)=0, the correct first bridge is

    L'(k+1,chi)/L(k+1,chi)
    + conjugate(L''(-k,chi)/(2 L'(-k,chi)))
      = EulerGamma + log(2 pi/q) - H_k.

The factor 1/2 is forced by the Taylor series of L(-k+z,chi)/z. For complex
characters the conjugation must be retained. At higher orders use the
regularized germ D(z)=L(-k+z,conjugate(chi))/z^nu, so
D^(j)(0)=j! L^(j+nu)(-k,conjugate(chi))/(j+nu)!.

The new article proves full jet transport and the parity-only character kernel.
This is a completion of a vague statement, not a claim that the original prints
an explicit formula with an incorrect factor 1/2.

## C4 — “Elementary remainder” does not match the displayed formula (scope correction)

**Location:** abstract; general duality prose; `eq:k2duality` near lines 287–311.

The abstract abbreviates the example as -256 pi^3 psi^(-3)(1/4) plus an
elementary remainder. Its actual displayed formula contains zeta'(3), zeta(3),
and log(A), with A the Glaisher–Kinkelin constant. No elimination of these
quantities to elementary constants is supplied.

**Proposed revision:** describe the actual residual as an explicit combination
of zeta jets, zeta values, Glaisher logarithms, and elementary terms. Likewise,
the expression beta'(-1)=2 Catalan/pi is a reduction to Catalan's constant, not
an established elementary evaluation.

This is not a proof that such constants can never have another reduction.

## Retained and not recertified

The harmonic-number master identity has a direct proof and is explicitly
credited to Coffey's earlier formula. The first-index distribution relation
and nonzero-value character bridge remain valid under their stated hypotheses.
The new zero arguments do not depend on the independence claim or the general
rank assertion. The original second-index rational tables are not rejected,
but this package does not certify every table entry.

`proposed_replacements.tex` supplies short replacement passages, intended for
manual review and insertion. It is not a standalone TeX article or an auto-patch.
