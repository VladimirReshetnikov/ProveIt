# Final integrated manuscript audit

Review date: 1 October 2026

## Conclusion

The final integrated TeX manuscript passes mathematical review. Its complete proof, the explicit first two corrections, the added next inverse term, the exact n=300 checks, and the fixed positive chromatic-parameter corollary are consistent with the independently audited argument. No unresolved mathematical blocker was found.

This addendum pins the integrated manuscript to these exact files:

- orientation-partition-asymptotics.tex
  SHA256 287644a8074901a4fc58e70269ac121e84a6df2d3076f53221be6246afee161c
- orientation-partition-asymptotics.pdf
  SHA256 bd3cd34aac1fba3a29a21d6c89d8e8cc042da50c15312c77c74e1d66b1656946

The detailed core audit is audit.md. The corollary analysis and endpoint-tail estimate are in fixed_parameter_audit.md. Those reports remain applicable to the final integrated source.

## Integrated proof checks

All core formulas were reviewed after translation to TeX: the exact finite Gamma identity, power-sum recurrence, uniform quadratic majorant, relative cutoffs, singular Euler-Maclaurin contribution, Fourier localization, prefactors, complete coefficient generator, Gaussian remainder control, and smooth-interpolant inverse and ceiling envelope.

The proof retains the crucial distinction between a fixed-total profile bound and the full generating product. The latter is controlled with the direct local-product expansion, rather than by applying the former outside its hypotheses. Its Bose-endpoint remainder polynomial explicitly vanishes at zero. The construction of exact interpolation uses logarithmic bumps, preserving positivity and asymptotic derivatives.

The added inverse formula was independently checked. If

    a=-C/ell,
    b=-alpha0-d0/ell+C^2/(2ell^2)-C^2/(2ell^3),

then the coefficient of N^(-1/2) in the logarithmic residual for x=N+a sqrt(N)+b+d/sqrt(N) is

    ell*d+(a+C/2)b-a^3/6-C*a^2/8+alpha0*a+beta1.

Setting this to zero gives exactly the printed d. The remaining logarithmic residual is O(N^(-1)), and division by the derivative, asymptotic to log N, proves inverse error O(1/(N log N)). The numerical inverse checks are appropriately identified as residual checks rather than certified rounding bounds.

The fixed-v corollary contains the explicit lower-tail integrability estimate needed when 0<v<1. The generalized Bernoulli-polynomial Gamma expansion and first correction are correct, and all claimed uniformity is confined to compact subsets of v>0.

The final minor descriptive edits are also correct: the second-order script uses the displayed root polynomials, the moment integrals are defined for j>=1, and the bibliography points explicitly to the cited arXiv v1.

## Scope of this signoff

This is a source-level mathematical audit with independent exact and high-precision numerical checks. It is not a machine-verification certificate, a rigorous interval certification of all displayed decimals, or an exhaustive historical-priority search. The finite-order Poincare qualification and the distinction between inverse envelopes and unconditional integer rounding must be retained. Visual PDF quality was checked separately during manuscript preparation.
