# Claims and validation boundaries

## New results argued in the article

1. **Atomic-phase fractional normal form (Theorem 2.1).** For every integer base `b>=2` and real exponent `s>1`, the pressure near zero equals
   `s log D_b(c) + log(1+|c|^s E_b,s(c))`,
   where `E` is positive, even, has every integer derivative of order less than `s`, and `E(0)=2(b^s-1) zeta(s)`.
2. **Exact integer differentiability class (Theorem 2.2 and Corollary 2.3).** Unless `s` is an even integer, the pressure is locally `C^(ceil(s)-1)` and the next derivative fails at zero. For binary pressure, `s=2q`.
3. **Sharp two-sided relaxation (Theorem 2.4).** The operator-norm difference between the atomic transfer iterate and its rank-one projector has the three regimes displayed in equation (2.17). Both the upper bound and a matching lower bound are proved. The endpoint logarithmic factor is necessary in this norm.
4. **All-base integer cancellation (Corollary 8.1).** The coefficient of `c^(2m)` vanishes for every integer base. The binary case is a previously established repository result, not a new priority claim.
5. **Locally uniform moment asymptotics (Corollary 9.1).** A positive amplitude and exponentially small relative error hold in a phase neighborhood of the atomic point, for fixed base and exponent.
6. **Critical atomic growth (Proposition 9.2).** At `s=1`, the atomic transfer powers applied to the constant function grow in supremum norm like `n+1`. This is not a critical-phase asymptotic theorem.

The theorem numbers above are those in the delivered source and PDF. In `C^alpha`, the endpoint `alpha=1` means Lipschitz functions, not the usual continuously differentiable Banach space.

## Mathematical dependencies

The proof rederives its atomic eigenfunction and transfer identities. It does not assume the truth of an informal repository result. The substantive steps are:

- telescoping of the digital mask;
- absolute convergence and differentiability of the periodized sinc power;
- explicit coefficient bounds and a matching power-sum lower bound;
- elementary isolated-eigenvalue perturbation via resolvents and a rank-one projector;
- a polynomial variation estimate identifying cylinder-supremum pressure with the eigenvalue;
- evaluation of the eigenfunction equation at the atomic fixed point;
- an absolutely convergent residue-class zeta sum.

The separate consequence for the phase-dependent L^q spectrum uses the pressure–spectrum identity from arXiv:2509.22109v1, Theorem 2.6. That external measure-theoretic result is not needed for the pressure theorem itself.

## What was actually checked computationally

The recorded default run performed:

- 112 atomic eigenfunction identity checks at 65-decimal-digit working precision;
- 28 amplitude identity checks at the same working precision;
- 20 exact symbolic integer-cancellation checks with symbolic base after removing the common zeta factor;
- 18 floating-point phase diagnostics and two doubled-grid comparisons.

All programmed assertions passed. The largest observed high-precision residuals are recorded in `results/verification.json`. Floating-point collocation uses a positive piecewise-linear interpolation and stops at the specified iteration tolerance; that tolerance is not a bound on the continuum discretization error.

The PDF was built with three successful pdfLaTeX passes. It was rendered and visually inspected. The final build had no undefined references, package warnings, or overfull boxes. See `results/build_validation.json` for the build environment and rendering receipt.

## Claims not made

- No Lean, Rocq, or other proof-assistant verification.
- No independent peer review.
- No interval-certified phase radius, spectral-gap constant, or discretization error.
- No exhaustive or definitive worldwide novelty/priority determination.
- No solution for phase asymptotics at `s<=1`, or regularity at every nonzero phase.
- No claim of optimal endpoint Hölder regularity on a whole phase neighborhood.
- No identification of the complete spectrum from an operator-norm estimate alone.
- No repository mutation, commit, or pull request.

The paper resolves a local part of the published stronger-regularity question; it does not assert that every aspect of the question is settled.
