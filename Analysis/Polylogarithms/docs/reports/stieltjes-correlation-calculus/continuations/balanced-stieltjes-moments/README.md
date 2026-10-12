# Balanced Stieltjes Moments
## Bernoulli Closure, Harmonic Filters, and Polylogarithmic Resonances

Research continuation prepared for Vladimir Reshetnikov and the ProveIt
project, 11 October 2026. The package contains a standalone LaTeX article,
compiled PDF, analytic proofs, exact algebra tests, high-precision numerical
diagnostics, and proposed integration material. No repository was modified.

## Main mathematical results

For the conventional generalized Stieltjes constants, define

\[
\mathcal C_q(x,a)=\frac{\log^{q+1}x}{q+1}
 +\sum_{j=0}^q(-1)^j\binom qj\gamma_j(x+a)\log^{q-j}x.
\]

The normalized homogeneous combination is unique in its stated ansatz, and
its first q inverse-power tails vanish. Its ordinary Mellin transform is

\[
\int_0^\infty x^{u-1}\mathcal C_q(x,a)\,dx
=\frac{\pi\zeta(1-u,a)}{\sin\pi u}
  q![z^q]\frac{\Gamma(u+z)}{\Gamma(u)\Gamma(1+z)},
\qquad a>0,\quad0<\Re u<q+1.
\]

For q >= m >= 1, every positive-integer moment is B_m(a) times an explicit
finite rational combination of ordinary zeta values. At B_m(a)=0 an additional
moment exists and is (-1)^(m-1) zeta^[1](1-m,a), with complete logarithmic
extensions and polylogarithm order-derivative coordinates.

For example,

\[
\int_0^\infty x^2\mathcal C_2(x,1/2)\,dx=\frac{3\zeta(3)}{16\pi^2},
\qquad
\int_0^\infty\mathcal C_q(x,1/2)\,dx=0\quad(q\ge1).
\]

A complete finite-shift convergence criterion and a two-variable Gamma germ
then evaluate all mixed logarithmic moments of polynomial-annihilating
Stieltjes filters. One consequence is

\[
\int_0^\infty[\gamma_1(x+1/2)-2\gamma_1(x+1)+\gamma_1(x+3/2)]\,dx
=\gamma_1+\gamma^2/2-\pi^2/24+3\log^2(2)/2-\log^2(\pi)/2.
\]

The article also gives all shift derivatives of the moments, anchored
primitives, further explicit zeta-derivative identities, and eight future
research directions. All displayed integral evaluations refer to the complete
combined integrands, not separately divergent summands.

## Files and reproduction

`article/Balanced_Stieltjes_Moments.tex` is self-contained and compiles to the
adjacent PDF. `integration/manuscript_fragment.tex` is an optional short
entry point; the source labels use the `bsm:` namespace. The full source
comparison and a verified editorial correction are documented in
`integration/SOURCE_AUDIT.md` and `integration/INTEGRATION.md`.

Run from this directory:

```sh
python -m pip install -r requirements.txt
python code/verify_exact.py
python code/verify_numeric.py
python code/verify_special.py
python code/verify_log_moments.py
python build.py
```

The mathematical scripts require Python, mpmath 1.3.0, and SymPy 1.14.0.
Building requires pdfLaTeX and the packages named in the source preamble.
The programs run offline after dependencies are installed. The build fixes
the PDF source date to the edition date. It performs no remote operation.

## Delivered verification

| Suite | Passed | Meaning |
|---|---:|---|
| Exact algebra | 823 / 823 | Exact rational/symbolic assertions, including two corruption controls |
| Main numerical | 34 / 34 | Combined-kernel quadrature, beta and recurrence checks, parameter refinement |
| Special-value numerical | 12 / 12 | Polylogarithm roots, closed constants, primitives, shift averages |
| Logarithmic-root numerical | 11 / 11 | Harmonic coefficient derivatives and ordinary logarithmic root moments |

The successful numerical suites contain **57 diagnostics**, primarily at
55 working decimal digits. The maximum reported scaled residual across the
successful suites is below 1.19e-53. This is not a rigorous error enclosure,
not a proof of 53 correct digits, and not a substitute for the analytic proofs.
The polylogarithm order derivatives use a 12th-order centered stencil at
85 digits, with two step sizes. The principal integral identities do not
use their proposed right sides to compute the quadrature side.

An earlier near-integer automatic-differentiation route failed three
polylogarithm diagnostics. Its report is preserved as
`results/exploratory_polylog_derivative_checks.json` and is excluded from
the passing totals. `code/demonstrate_order_derivative_issue.py` reproduces
the original diagnostic route. The corrected, step-refined implementation
is in `code/verify_special.py`. The analytic proof uses the Hurwitz Fourier
identity and does not depend on either numerical method.

## Scope and originality

Analytic proofs are supplied; no proof-assistant formalization or independent
peer review is claimed. The classical beta, Gamma, Euler–Maclaurin, and
Hurwitz functional equations are explicitly credited. The all-order balanced
organization and its consequences are proposed research additions, not a
certification of literature priority.

The source audit was targeted. The incoming directory was inventoried but
its binary archive interiors were not inspected. The article does not
resolve S6, revised S8, or the distinct harmonic Stieltjes coefficients
R_{r,k}. A duplicated paragraph in the pinned canonical README was confirmed;
no mathematical error in the inspected predecessor statements was established.

`SHA256SUMS` covers the delivered package files other than itself. Rebuilding
or rerunning the programs will change generated-file checksums; regenerate
the manifest for a new release.
