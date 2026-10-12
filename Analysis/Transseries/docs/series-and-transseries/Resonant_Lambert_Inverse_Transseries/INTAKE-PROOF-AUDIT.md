# Resonant Lambert inversion: proof review, 12 October 2026

The delivered article has been read and its conventional arguments accepted
for a separate collective synthesis. This symmetric two-index Lambert family
differs from the single-polylogarithm analytic-tail models. The source,
authored PDF, original code and supplied evidence remain unchanged.

The Mellin representation and a fixed enclosing contour handle the triple
collision uniformly in the order parameter. Centering removes the next-to-
leading logarithmic coefficient. Reflection before differentiation gives
the hypergeometric divisor kernel and the second-jet odd-power activation.
The projected jet jump is pi^2/2 times the base jump; this is not an identity
for the entire second jet. Normal convergence is on the stated slit domains.

The real Borel completion is identified by a Mellin integral, rather than
inferred from reality or a formal expansion. The logarithmic singularities
are integrable and the divisor tail has a summable majorant. The arcsinh
chart is convergent for the singular core. Its two displaced complex folds
are core folds; full-function complex folds remain unproved.

The auxiliary-variable Lagrange formula gives the rational inverse-sector
polynomials with the stated signs, valuations and Catalan top coefficients.
The same-sign even subsequence proves ordinary radius zero for fixed u>0;
the factorial-composition upper bound and that lower bound give Borel radius
4*pi^2. Pringsheim applies at the negative Borel endpoint after changing the
sign of the argument. This does not prove global inverse Borel continuation.

For the actual lateral inverses, Rouche on a disk of radius c*t^2 gives
holomorphic dependence on a Stokes parameter on a disk larger than 1.
The Lagrange transport formula is therefore convergent at both lateral
values. Its odd and even parts yield the nested splitting and arithmetic
averaging defect. Differentiating the controlled exponential-integral
remainder gives the leading coefficient -1 of the second-action defect.
Arithmetic averaging is not identified with nonlinear median summation.

The full unchanged verifier passed on a separate copy: exact substitution
through q^8, centered normalizers, reflected coefficients and order jets,
core/fold diagnostics, optional SciPy Mellin quadrature, and all three
lateral inverse checks at 80, 125 and 205 working digits. Python 3.13.5,
SymPy 1.14.0, mpmath 1.3.0 and SciPy 1.17.0 were used. Fresh outputs and
the actual run log are in intake-verification. Quadrature estimates and
rounded zero root residuals are not exact or interval certificates.

The conjectural cosh/sinh large-order amplitudes remain open: fixed-factor
asymptotics do not justify summing over a growing number of factors. Full
inverse Borel continuation and full complex folds likewise remain open.
The canonical integration should follow the completed Lambert forward
identities and distinguish its divergent sector series from convergent
core charts. No collective or Transseries PDF was rebuilt in this intake,
and no Lean formalization is claimed.


## Subsequent resolution, 12 October 2026

The conventional proof review of [summation and singularities](continuations/summation-singularities/INTAKE-PROOF-AUDIT.md)
resolves the cosh/sinh coefficient conjectures left open at the time of
the review above. It supplies a uniform first correction and explicit
logarithmic/dilogarithmic Borel boundary models. Global continuation is
not inferred from those boundary models. The parent delivered article
and its original conjectural wording are preserved as source evidence.
