# Proposed ProveIt integration

## Placement

Preserve the original package as an incoming ZIP. After full overlap and proof
review, a suitable canonical destination is a new chapter or section on
**vertical-line Hurwitz pairings**, near the existing integration/log-Gamma
material. Do not merge its ordinary real-line integrals into the periodic
finite-part/contact chapter without an explicit change of geometry.

Suggested new file name (proposal only, not an existing repository path):
`chapters/07-vertical-hurwitz-pairings.tex`.

## Dependencies and insertion order

1. Branch conventions and the classical Hurwitz/Lerch Mellin representations.
2. Bilinear/scaled Laplace–Plancherel lemma.
3. Basic K function, all-index Stieltjes coefficients, and complex-safe Hermite formula.
4. Finite harmonic, polygamma, and colored Lerch consequences.
5. Bernoulli depth hierarchy, finite closure, Stirling norm, and normalized primitives.
6. Rational slopes, residue grid, explicit jet coefficients, and finite resonance evaluator.

Use a fresh canonical label prefix, e.g. `vsh:`, when transplanting labels.
The standalone article intentionally has its own notation and numbering.

## Collision/notation guards

- Here `Z_s(z)=zeta(s,z)-z^(1-s)/(s-1)` is a **spatially compensated** Hurwitz family. It is not the auxiliary `zeta(s,z+1)` of some finite-interval product papers.
- The variable on the integration line is the imaginary part of `z`, not of `s`.
- `F_d=Gamma(s) R_d` is evaluated by its combined continuation. The Gamma factor must be retained at negative spectral integers.
- `J_{d,e}` and `J_{d,e}^{p,q}` are holomorphic Mellin transforms in their stated domains; the individual terms in their finite expressions need not be finite.
- Analytic log-Gamma is required; principal `log(gamma(z))` is not a replacement.
- In the scaled identity with vertical slopes `(p,q)`, the weighted position is `B=q*a+p*b`, and the spectral prefactor is `q^(s-1)*p^(t-1)`.
- The all-index scaled formula includes `q^u*p^v`. Omitting these factors loses logarithmic slope terms.

## Verification promotion

The exact finite replay should remain separate from unvalidated numerical
quadrature. Record the known mpmath 1.3.0 nonreal-argument limitation next to
any use of that backend. The present code uses Hermite/Cauchy alternatives
for nonreal arguments and retains a positive-real control.

Before canonical integration, compare the complete text of recently arrived
Mellin–Hurwitz and mixed-spectral reports, not merely their metadata. This
package does not certify that exhaustive comparison. No changes to S6/S8
status should follow from this article.

No repository mutation has been performed. These are proposed integration
instructions, not a claim that the work has already been merged.
