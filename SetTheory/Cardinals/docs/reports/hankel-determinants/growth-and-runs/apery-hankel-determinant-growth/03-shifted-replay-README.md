# Replay: Apéry Hankel determinants with proportional shifts

This small, standalone package reproduces the numerical and symbolic checks
accompanying the article. It contains no repository snapshot or source PDFs,
and it does not contact any external service. The finite checks support the
normalizations and numerical comparisons; they do not prove the analytic
theorem and are not interval certificates.

## Run

Python 3.12 is recommended. From this directory, in an environment with the
dependencies installed:

```sh
python3 -m pip install -r requirements.txt
python3 -m unittest discover -s tests -v
python3 verify_symbolic.py
python3 check_shift.py --s 0.1 --M 1024 --N 20,40,80
python3 check_shift.py --s 0.2 --M 1024 --N 20,40,80
python3 check_shift.py --s 1 --M 512 --N 20,40,80
python3 verify_c1_log_shift.py
python3 check_first_correction_trace.py
python3 evaluate_c1.py --s 1 --M 256
python3 evaluate_c1.py --s 1 --M 512
```

For a complete repeat, including the two coefficient grids, corrected
residuals, all tests, and comparison with the supplied reference results:

```sh
python3 run_replay.py --stability
```

This writes fresh outputs under `generated/`. It preserves `expected/` and
`recorded/`. The optional `--stability` doubles each quadrature grid and
independently repeats each order-80 determinant at 320 and 400 decimal
digits. Use `--output another-directory` to choose a different destination.
No script downloads its dependencies automatically.

## Contents

- `density.py`: only Edgar's upper-band hypergeometric density and its
  right-endpoint normalization, with the necessary continuation sheet
- `check_shift.py`: exact integer moments, high-precision normalized Hankel
  elimination, the exact Jacobi gamma-product reference, and midpoint/DCT
  evaluation of the perturbation constants
- `verify_symbolic.py`: finite exact algebra and equilibrium-mass quadrature
- `evaluate_c1.py`: derivative quadrature for the explicit first correction,
  plus decimal arithmetic for its corrected logarithmic residual
- `verify_c1_log_shift.py`: exact first-correction check for a logarithmic
  perturbation, using the independently expanded Selberg exponent shift
- `check_first_correction_trace.py`: exact first-correction check for a
  linear perturbation, using finite-N Schur/Selberg trace cumulants
- `tests/test_replay.py`: eleven tests covering binomial moments, determinant
  scaling, the Jacobi beta-moment determinant, the cosine coefficient
  convention, density branch continuity and endpoint value, parameter
  validation, numerical regression, symbolic identities, and both exact
  first-correction comparisons, and the equivalent cubic formula
- `run_replay.py`: reproducible runner and recorded-reference comparison
- `expected/`: the three original numerical reference outputs and the
  symbolic reference output (augmented with an explicit correction-scope
  label), plus the original 256/512-node first-correction outputs and
  corrected-residual reference
- `recorded/`: a fresh execution of this standalone package and its timing,
  dependency-version and numerical-stability report

The package computes the explicit first correction, not an all-orders
coefficient recursion. Higher-order continuation is a method described in
the article. The symbolic file's `barnes_first_log_correction` remains only
the coefficient for the unperturbed Jacobi gamma product; the Apéry
corrections are `c_rel` and `c_full` in the separate coefficient outputs.
The numerical column `N_times_error` is a rescaled residual, not a value of
the correction obtained by fitting.

## Mathematical conventions

The matrix order is **N**, not N+1. With

\[
C=17+12\sqrt2,\qquad
A_k=\sum_{j=0}^k\binom{k}{j}^2\binom{k+j}{j}^2,
\]

the computed determinant is

\[
\overline D_N^{(r)}
 =\det\left[\frac{A_{r+i+j}}{C^{r+i+j}}\right]_{i,j=0}^{N-1}
 =C^{-N(r+N-1)}\det[A_{r+i+j}]_{i,j=0}^{N-1}.
\]

The reference determinant for the weight \(t^r(1-t)^{1/2}\) on \([0,1]\) is

\[
J_N(r)=\prod_{j=0}^{N-1}
 \frac{\Gamma(j+1)\Gamma(r+j+1)\Gamma(j+3/2)}
 {\Gamma(r+N+j+3/2)}.
\]

The Hankel-integral factor \(1/N!\) is already included in this expression.
The script requires \(r=sN\) to be an integer and does not silently round it.
Decimal strings and rational strings such as `--s 1/10` are accepted.

Set \(a=(s/(s+2))^2\),
\(t(\theta)=(1+a)/2+(1-a)\cos\theta/2\), and
\(f(t)=\log(C\phi(Ct)/\sqrt{1-t})\), where \(\phi\) is Edgar's density.
Here `f1` means the endpoint value \(f(1)\), whereas `f0` means the
zeroth cosine coefficient. For the coefficients

\[
f_k=\frac1\pi\int_0^\pi f(t(\theta))\cos(k\theta)\,d\theta,
\qquad f(t(\theta))=f_0+2\sum_{k\ge1}f_k\cos(k\theta),
\]

the program uses

\[
F=\frac1\pi\int_0^\pi
 f(t(\theta))\frac{(s+2)(1-a)\cos^2(\theta/2)}{2t(\theta)}\,d\theta,
\quad B=\frac{f_0-f(1)}4,
\quad Q=\frac12\sum_{k\ge1}k f_k^2,
\quad E=e^{B+Q}.
\]

In the JSON, `bias` denotes \(B\). In particular, applying this cosine
convention to \(f(t(\theta))=\cos\theta\) gives \(Q=1/8\); a unit test checks
that factor. The tabulated residual is

\[
\delta_N=\log\overline D_N^{(sN)}-\log J_N(sN)-NF-\log E.
\]

The density module is deliberately restricted to \(1/C<x<C\). Accordingly
the numerical script requires
\(s>s_* = 3\sqrt2/4-1\approx0.06066017\), so its entire integration band
lies to the right of the density's interior singularity. It does not cover
the critical or subcritical regimes.

## Expected values

Only enough digits for a useful numerical comparison are shown here; see
`expected/` for the original machine outputs.

| s | F | E | delta at N=20 | delta at N=40 | delta at N=80 |
|---|---:|---:|---:|---:|---:|
| 0.1 | -0.404401173409 | 2.285724816454 | 0.001608462316 | 0.001686953354 | 0.000751788540 |
| 0.2 | -0.518860339551 | 1.938568386491 | 0.000839079936 | 0.000569348565 | 0.000324954543 |
| 1 | -0.905280469462 | 1.351121825796 | 0.001005620781 | 0.000509359003 | 0.000256302053 |

### Explicit first correction

Hold the analytic function f fixed while varying the left endpoint u, and
define

\[
U(u)=\frac1\pi\int_0^\pi
 f\!\left(\frac{1+u}{2}+\frac{1-u}{2}\cos\theta\right)d\theta,
\qquad S(u)=\sum_{k\ge1}k f_k(u)^2.
\]

Thus \(U(a)=f_0\) and \(S(a)=2Q\). All primes below are derivatives with
respect to u at u=a, **not** derivatives with respect to s. Set
\(D=2a^{3/2}(1-a)U'(a)/s\). The implemented coefficient is

\[
c_{\rm rel}(s)=\frac{D S'(a)}6+\frac{D U'(a)}8
 +\frac D{24}\left(\frac1{1-a}+\frac3{2a}\right)
 +\frac{a^{3/2}}{12s}\big((1-a)U''(a)-U'(a)\big),
\]

with elementary/Barnes-normalized coefficient

\[
c_{\rm full}(s)=c_{\rm rel}(s)
-\frac1{48}\left(1+\frac1{s+1}-\frac1{s+2}\right).
\]

The general analytic endpoint-variation identity
\(S'(a)=-(1-a)[U'(a)]^2/2\) gives the equivalent cubic expression

\[
c_{\rm rel}(s)=\frac{\sqrt a(1-a)}{24s}
 \left[-4a(1-a)(U'(a))^3+6a(U'(a))^2+3U'(a)+2aU''(a)\right].
\]

The evaluator retains the independently summed DCT derivative S' for its
original computation, then also reports `c_rel_simplified`,
`S_prime_identity_residual` and `c_rel_formula_difference`. Thus the
simplification is checked numerically rather than silently replacing the
energy calculation. A unit test checks the exact algebra of the cubic
substitution and its numerical agreement at s=1. These finite checks do
not establish the general analytic endpoint identity by themselves.

At s=1 the reference 512-node evaluation gives
\(c_{\rm rel}=0.020633150203337213125\) and
\(c_{\rm full}=-0.0036724053522183424301\). These long strings preserve
the computation; they do not claim twenty correct digits. Using the
256-node coefficient, the corrected logarithmic residuals are:

| N | delta_N - c_rel/N | N squared times corrected residual |
|---|---:|---:|
| 20 | -0.0000260367286881 | -0.0104146914752 |
| 40 | -0.00000646975257906 | -0.0103516041265 |
| 80 | -0.00000161232493800 | -0.0103188796032 |

The two exact symbolic checks are independent test perturbations of the
same functional. For \(f(t)=\gamma\log t\), the exact Selberg exponent shift
gives

\[
c_{\rm rel}=\frac{\gamma(-8\gamma^2+6\gamma s+3s+4)}{24s(s+1)(s+2)}.
\]

For \(f(t)=\lambda t\), Schur/Selberg moments give the order-1/N coefficients
of the mean, variance and third cumulant of \(\sum_jt_j\), respectively,

\[
\frac{s+1}{4(s+2)^3},\qquad
\frac{s^2(s+1)}{2(s+2)^5},\qquad
-\frac{2s^2(s+1)^2}{(s+2)^7}.
\]

Their combination with multipliers \(\lambda,\lambda^2/2,\lambda^3/6\)
agrees identically with the formula for \(c_{\rm rel}\). These checks test
normalization and response terms, not the article's analytic remainder.

The symbolic checks return `PASS`,
\(s_*= -1+3\sqrt2/4\), the logarithmic power \(-1/24\) through exact Barnes
factor cancellation, and equilibrium-mass errors below \(10^{-55}\) in the
four tested cases. A displayed `0.0` is a rounded floating-point result, not
an exact quadrature certificate.

### Fresh execution included here

The 2 October 2026 run used Python 3.12.14 and the pinned dependency
versions. All eleven tests passed, and all listed constants and determinant
residuals reproduced the numerical reference files exactly. The full run,
including coefficient differentiation and all stability checks, took
**28.86 seconds**. Detailed timings are recorded in
`recorded/validation_report.json`. These are observed timings, not runtime
guarantees.

Grid doubling changed F by at most 2.23e-16 and any of F, f0, bias, Q, E by
at most 4.45e-16. The absolute differences between the order-80 logarithmic
determinants evaluated at 320 and 400 decimal digits were approximately
2.22e-199, 2.39e-194 and 9.30e-161, respectively. These checks show that,
for these cases, the float64 constant evaluation is the practical accuracy
limit. They do not turn the displayed decimals into rigorous enclosures.
See `recorded/validation_report.json` for the full measurements.

## Precision and interpretation

- Hypergeometric values are evaluated with 40 decimal digits by default;
  `--density-dps` changes that working precision. The quadrature values are
  then converted to binary64 for SciPy's DCT and NumPy's weighted sum.
  Consequently the reported constants are **not** 40-digit results.
- Integer moments are exact. The default determinant precision is
  `max(120, 4*N)` decimal digits. `--dps` overrides it. This is a practical
  working choice, not a condition-number bound. A nonpositive elimination
  pivot raises an error; positive pivots alone do not establish accuracy.
- Twenty printed digits in residual strings are formatting, not twenty
  validated digits. Error in F is multiplied by N. Compare a larger grid
  and a higher determinant precision before using larger N or different s.
- First-correction differentiation uses mpmath at 45 working decimal
  digits by default, followed by float64 transforms and averaging. Its
  coefficient has the same non-certified floating-point limitation; a
  256/512-node comparison is recorded separately.
- Grid doubling and increased-precision comparisons are empirical
  stability checks only. A small final DCT coefficient alone is not a
  bound on truncation, aliasing or roundoff error.
- Convergence can be slower near s*. The order-20/40 residual at s=0.1 is
  not monotone. Three finite determinants establish neither an asymptotic
  rate nor a coefficient of the next term.

## Attribution and provenance

The mathematical density is due to G. A. Edgar, *The Apéry Numbers as a
Stieltjes Moment Sequence*, arXiv:2005.10733v2 (2020), particularly
Propositions 23 and 25:
<https://arxiv.org/abs/2005.10733v2>.

The explicit hypergeometric continuation prescription follows the targeted
script `code/02-szego-density_constant.py` in Vladimir Reshetnikov's ProveIt
report *Apéry Hankel growth: a proof, sharp Szegő asymptotics, and reproducible
computations*. The inspected repository context is revision
`946b6c762da4f5e0f7b8816facbe15920fcce270`:

<https://github.com/VladimirReshetnikov/ProveIt/blob/946b6c762da4f5e0f7b8816facbe15920fcce270/SetTheory/Cardinals/docs/reports/hankel-determinants/growth-and-runs/apery-hankel-determinant-growth/code/02-szego-density_constant.py>.

`density.py` is a small adaptation of the needed formulas and branch rule;
it omits that script's left-band formula, endpoint angle cutoffs, global
quadrature and unrelated outputs. The accompanying numerical and symbolic
checks have been reorganized into importable functions and tests. No full
repository material is required or bundled. No claim of a new density
formula, interval verification or formal proof is made.

The trace check's finite-N Schur average is equation (4.1) in Albion,
Rains and Warnaar, *Elliptic A_n Selberg Integrals*,
<https://doi.org/10.1007/s00365-025-09705-8>. It is used to derive the first
three trace moments and cumulants, separately from the article's
potential-variation calculation. Only the numerical and symbolic check
code and its results are included here.
