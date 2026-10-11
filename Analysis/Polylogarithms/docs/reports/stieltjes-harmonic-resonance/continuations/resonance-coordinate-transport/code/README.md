# Verification code

The scripts accompany the article's proofs. They check exact finite algebra
and compare independent numerical representations; they do not constitute
a formalization of the analytic theorems or interval certificates.

## Run from the package root

The recorded environment used **Python 3.12.14**, **mpmath 1.3.0**, and
**SymPy 1.14.0**. The dependency file pins the two tested Python packages.

```bash
python -m pip install -r requirements.txt
python code/verify_all.py
```

The runner uses the current Python interpreter, runs all three scripts
sequentially with the package root as their working directory, and streams
their output. It stops at the first failed process and returns its nonzero
status (or the conventional signal-derived status). The numerical transport
script's Mellin check is included. Child-process assertions are enabled even
if `PYTHONOPTIMIZE` was set in the runner's environment.

The individual commands are:

```bash
python code/verify_dougall.py
python code/verify_nonlinear.py
python code/verify_transport.py
```

For a deliberately reduced transport run, omitting its independent Mellin
integral comparison:

```bash
python code/verify_transport.py --skip-mellin
```

The independent cutoff calculation can also be run separately:

```bash
python code/independent_cutoff.py
```

It is already called by `verify_nonlinear.py`. Direct script runs should use
ordinary Python execution, without `-O` or `PYTHONOPTIMIZE`, because the
scripts use assertions. Reports are written beneath `results/` and replace
the previous report with the same name; a reduced transport run therefore
replaces the full transport report with its reduced result. The scripts
require no network access and write no article files.

## What each verifier checks

| Script | Method and supplied coverage | Report |
|---|---|---|
| `verify_dougall.py` | Exact symbolic coefficient differential and residue identities through index 2; 19 numerical comparisons at 75 decimal digits, including integer and half-integer resonances, first and second jets, both binomial families, and reciprocal-Gamma degeneracies. | `results/dougall_checks.json` |
| `verify_nonlinear.py` | 138 exact finite-algebra cases; an independent source-coordinate cutoff calculation on 48 nonlinear coordinate cases and 140 monomial pairings. | `results/nonlinear_checks.json` |
| `verify_transport.py` | Four exact Bernoulli-polynomial integral identities; 13 numerical checks at 45 decimal digits, including pointwise multiplication, ambient finite parts, unequal-frequency lifting, lower-term simplification, and an independent six-cone Mellin comparison. | `results/transport_checks.json` |
| `independent_cutoff.py` | Standalone inverse-coordinate and inverse-Jacobian primitive calculation, also embedded in the nonlinear verifier. | `results/independent_cutoff_checks.json` when run separately |

The Dougall numerical summation uses 120 direct terms and a finite centered
asymptotic tail through coefficient `C_11`. Its recorded largest absolute
discrepancy is approximately `3.76169e-36`, against an acceptance threshold
of `1e-31`. This finite tail completion is an approximation, not a certified
remainder bound. The transport verifier records a tolerance and scaled
error for each comparison. Working precision and observed agreement are
not rigorous error enclosures. Exact SymPy identities certify the specific
finite expressions tested; the paper supplies the general analytic proofs.

### Spectral-derivative precision caveat

At 75 digits, generic differentiation of
`lambda s: mp.zeta(s, mp.mpf('0.25'))` at `s=0`, order two, produced a
discrepancy of about `2.29e-15` in this environment. Native
`mp.zeta(s, a, derivative=k)` agreed with an independent Cauchy-circle
derivative and restored the summed identity to about `4.47e-45`.
The Dougall verifier therefore uses native Hurwitz spectral derivatives.
Increasing the global precision alone should not be assumed to validate a
generic differentiation route at a special argument.

## Reusable functions

These research routines expose useful calculation functions. They are not
a packaged general-purpose special-function library: the caller must
respect the domains in the article and the distinctions between Taylor
coefficients, derivatives, distribution coefficients, and test pairings.
Use exact SymPy rationals or `fractions.Fraction` for exact arguments and
construct high-precision numbers from strings rather than binary floats.

### Dougall calculations: `verify_dougall.py`

- `coefficients(a, b, c, u, count)` returns centered coefficients
  `C_0(u), ..., C_(count-1)(u)` using the Bernoulli recurrence.
- `r(n, a, b, c, u)` evaluates the Gamma-normalized summand using entire
  reciprocal-Gamma factors.
- `completed_series(a, b, c, u, K, cutoff=120, terms=12)` numerically
  evaluates the bracketed subtraction with a finite asymptotic tail.
  Use `terms > K`; this routine supplies no certified error bound.
- `analytic_E(a, b, c, N, t)` evaluates the holomorphic factor
  `2*t*G(-N+t)` through finite Gamma shifts, retaining moving zeros.
- `jet_formula(a, b, c, N, m, K=None)` evaluates the proved resonant
  **Taylor coefficient** `[t^m] R_K(-N+t)`. The default is `K=N+1`;
  otherwise require `K>N`. Multiply by `m!` for the raw derivative.

The article assumes `a,b,c>0`, `d0=1+a-b-c>0`, and the stated convergence
strip. Importing this module sets `mp.mp.dps=75`; set it explicitly again
if composing the functions with another numerical workflow.

### Nonlinear finite parts: `verify_nonlinear.py`

`coordinate_correction(n, r, normalized_jet, scale=1, log_scale=None)`
returns the coefficients of `delta, delta', ..., delta^(r)` for the
article's scalar-distribution pullback correction. Use nonnegative integer
`n,r`, a positive real `scale`, and a SymPy polynomial or series in the
module's symbol `t` whose constant term is one. Terms above degree `r`
are irrelevant. The optional `log_scale` permits exact symbolic treatment
of the logarithm independently of the scale.

For example, from the package root:

```python
from pathlib import Path
import sys
import sympy as sp

sys.path.insert(0, str(Path('code').resolve()))
from verify_nonlinear import coordinate_correction, t

correction = coordinate_correction(
    n=0, r=1,
    normalized_jet=1 + sp.Rational(2, 3)*t,
)
```

In `independent_cutoff.py`, `inverse_jet(f, degree)` constructs the inverse
coordinate jet. `primitive_cutoff_values(n, r, f, g=None)` independently
computes the correction's pairings with `1,t,...,t^r`. Those pairings
are not the delta coefficients themselves: a coefficient `c_j` of
`delta^(j)` pairs with `t^j` as `(-1)^j*j!*c_j`. Use that module's own
symbol `t` when constructing `f`.

### Frequency transport: `verify_transport.py`

- `polynomial_hurwitz_integral(ps, aa, degrees)` exactly integrates the
  product `zeta(-degrees[j], {ps[j]*x+aa[j]})` on the unit interval by
  piecewise Bernoulli polynomials.
- `finite_part_gamma0(ps, aa)` directly computes the ambient-coordinate
  finite part of a product of `gamma_0=-digamma`, using local subtraction
  and quadrature rather than the multiplication formula.
- `triple_lift_000(ps, aa)` evaluates the finite unit-frequency lifting
  formula, including its lower-order corrections, for three factors.
- `tornheim_mellin(A, B, C, x, y)` evaluates a colored Tornheim kernel
  through its Mellin integral where that integral converges. The supplied
  check uses `A=B=C=2`.

Pass positive integer frequencies `ps` and `Fraction` shifts `aa`; the
singular grids must be disjoint for these routines. Set `mp.mp.dps`
explicitly before calling numerical functions independently; the script's
`run()` sets it to 45. The exact polynomial routine returns a SymPy exact
expression, not a floating-point approximation.
