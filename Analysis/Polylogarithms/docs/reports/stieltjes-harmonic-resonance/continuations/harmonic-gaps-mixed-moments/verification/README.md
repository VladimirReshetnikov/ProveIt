# Verification methods

The article contains the proofs. These programs provide exact checks of finite identities and numerical diagnostics of sensitive specializations. Their result records are in `../results/`.

## Exact finite calculations

`verify_zero_block_kernel.py` uses Python `Fraction` only. Positive rational fourth roots of the exponential nodes allow quarter-integral endpoints, including genuinely nonintegral endpoint differences, without floating-point evaluation. It compares the explicit divided difference with independent endpoint composition, the infinite-tail convolution, a kernel recurrence, finite exponential sums, inverse intervals, direct zero-block sums, and the insertion identity. There are 590 assertions.

`identity_moments_verify.py` uses exact SymPy rational algebra for 400 boundary cancellations and 60 finite summation-by-parts identities. The latter treat the two initial tail values as independent symbols. It implements the finite Bernoulli moment formula and the classical Euler reduction in a formal ordinary-zeta alphabet. No independence of the corresponding numerical zeta products is assumed.

## Numerical comparisons

The moment script separately computes direct finite Hurwitz-zeta heads and centered asymptotic tails. It uses two cutoff/truncation pairs, `(N,K)=(48,32)` and `(64,36)`, at 95 decimal working digits, for 30 cases. Tail truncation errors are observed through independent comparisons; no interval enclosure is asserted.

`identity_generator_verify.py` compares three implementations: anchored quadrature of the forcing ODE, the finite polylogarithmic primitive, and a Taylor sum formed from 65 exact moment coefficients. The three cases include a nonreal argument. The asserted absolute diagnostic tolerance is `1e-80` at 95 working digits.

`verify_r8_audit.py` checks 15 cases at 65 working digits: finite moving-index sums against Hurwitz/Gamma gaps; convergent paired weighted tails against an independently accumulated relative ordered sum; the Barnes specialization; finite negative-outer Bernoulli formulas; and a deliberate continued-versus-literal boundary difference. The truncated noninteger-endpoint comparisons retain their observed truncation residuals.

`verify_mellin_derivatives.py` tests the normalized Mellin lemma against two independent functions `f(y)=exp(-c*y)P(y)`, where `P` is quadratic and one case has complex data. Their Mellin transforms are elementary and entire:

```text
M_f(u) = c^(-u) [p0 + p1*u/c + p2*u*(u+1)/c^2].
```

The script differentiates this expression and compares it with subtracted logarithmic integrals of analytically computed `f^(m)`. The near-zero subtraction uses `expm1`; the logarithmic endpoint is handled by a change of variable. It tests `m=0,1,3` and `r=1,2,3,4` for each function, giving 24 cases at 80 working digits. This checks the lemma independently; it is not direct quadrature of the relative harmonic triple integral.

## Reproduction

Run `python3 verification/run_all.py` from the package root, or run any script individually. The default output paths resolve relative to the scripts, so the programs can also be invoked from another working directory. `verify_zero_block_kernel.py` accepts an optional positional output path; `verify_mellin_derivatives.py` accepts `--output`.

The recorded total is 1,050 finite exact assertions and 72 numerical cases. Each numerical case can contain more than one residual comparison; the count refers to cases, not decimal digits or Taylor coefficients. The general analytic statements, endpoint continuation, and convergence of the full generating functions are proved in the article.
