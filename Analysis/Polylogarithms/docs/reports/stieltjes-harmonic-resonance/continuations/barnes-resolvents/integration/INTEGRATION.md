# Integration notes

## Baseline

Repository: VladimirReshetnikov/ProveIt.
Revision: `7bd45777a8a127e5dc69aff8887ca36a79a3059d`.
Recorded commit time: 2026-10-11 01:57:13 UTC.
The source inventory identifies the inspected manuscript and all incoming archives.

This package adds a research article and reproducible computations. It does not
modify repository files or provide formal ProveIt theorem implementations.

## Suggested insertion order

1. **Polynomial Hurwitz transform (Section 2).** Place after the existing
   cotangent-resolvent Fourier lemma. The only genuinely additional analytic
   object needed for polynomial weights is the coupled depth-two series
   `O_{alpha,beta}(q)`. Its subtracted versions `U_j,V_j` give the Stieltjes
   germ and constructive continuation to every required negative order.
2. **Individual multiple Gamma functions (Section 3).** This depends on
   Section 2 and the classical Barnes/Hurwitz conversion. Preserve the
   coefficient polynomials `C_{r,k}`, normalization `Q_r`, and division
   convention `Gamma_1=Gamma`, `Gamma_2=1/G`. The real Barnes-G component
   is useful as an independently readable exact-identity corollary.
3. **Complex powers (Section 4).** This can follow the completed Stieltjes
   generator in the incoming Parity report. Preserve the continuous branch
   of `Log(K-z)`, the phase of `sigma`, the completion at `s=0`, and the
   full amplitude subtracted at a positive integer crossing.
4. **Quartic harmonic bridge (Section 5).** Place after the cubic
   digamma–harmonic bridge. This is separate from the quartic directional
   Tornheim calculation. Strict harmonic prefixes `H_{n-1}` and
   `H_{n-1}(1,1)` are essential to the displayed constants.
5. **Transverse cyclic data (Section 6).** Place after the previously
   defined holomorphic remainder `R` and symmetric germ `J`. Preserve
   their exact old normalization. The new contribution is the explicit
   ordinary convergent integral and the resulting fifth-order formula.

Use the modular section files when merging. The standalone file is the
portable complete article, not a second independent source to maintain.
Every LaTeX label and bibliography key is prefixed `bhr:`. Theorem and
equation numbers are local to this article; references should use labels.
The preamble's generic convenience macros may be mapped to the manuscript's
existing macros rather than imported twice.

## Critical conventions

- `zeta(1-s,x) = -1/s + sum gamma_m(x)*s^m/m!`; hence `gamma_0=-psi`.
- Finite parts are constant coefficients in the original x cutoff. A
  Laurent constant in an auxiliary parameter requires the proved correction.
- Unit-period Barnes zeta is written `mathcal Z_r`; strict harmonic
  Dirichlet series in Section 5 are written `Z_d`.
- In Section 6, `mathfrak g(C)=1/Gamma(1+C)` and `kappa_2=zeta(2)`;
  these avoid conflicts with the Barnes function `G` and the resolvent `q`.
- The coupled nested function at colors `(q,q^{-1})` is defined by the
  convergent double series. Individual colors must not be checked for
  convergence independently of their cumulative products.
- A q derivative of the depth-two series may be written as a paired
  difference whose individual terms diverge. Keep the combined summand
  or use its continued difference; do not split it numerically.

## Claims to keep open

The current `cycloquot:conj:S6` and `s8new:conj:S8` remain conjectural.
The old rejected S8 vector is a different candidate. No assertion of
arithmetic independence or a finite ordinary-zeta evaluation of the
remaining harmonic/Tornheim coordinates follows from this article.

The complex-power generator is jointly meromorphic for all complex
parameters. Its proved comparison with pointwise x-finite parts covers
`Re(lambda)>0`. Negative integer exponents have additional two-endpoint
phase contributions. Products of multiple-Gamma logarithms and arbitrary
incommensurable Barnes periods are further questions, not consequences
of the individual unit-period theorem.

## Verification and reuse

The article supplies the analytic proofs. There are 43 finite exact
symbolic checks across the Barnes normalization, quartic, and cyclic
branches, plus independent numerical programs. The numerical records
are diagnostics, not rigorous enclosures of constants.

Only `verification/cyclic/tornheim_mellin.py` is copied from an earlier
incoming report; its provenance and original attribution are preserved.
All other verification scripts in this package were prepared for this
continuation. The package hash manifest should be regenerated after
integration edits. No automatic change to existing conjecture status
or validation metadata is proposed.
