# Numerical reproduction

Run from the package root:

```sh
python code/verify_recurrence.py --nmax 1000
python code/verify_symbolic.py
```

The script uses Python, mpmath, SymPy, NumPy, and SciPy. The versions used for
the supplied data are recorded in `data/diagnostics.json`. The default run took
about 17 seconds on the execution machine. Runtime depends on hardware and
library configuration.

Both programs write into `rerun/` by default, preserving the supplied recorded
data. Use an explicit `--out` option to choose a different destination.
For the numerical program, `--out` names a directory; for the symbolic
program, it names the JSON output file.

The symbolic program checks the displayed finite Taylor coefficients through
Q4, independently reconstructs c0–c4 from Gamma logarithmic moments, verifies
the exact finite geometric remainders through order 12, checks the inverse
error-law coefficient algebra, and records exact rational witnesses for the
scalar inequalities used in the conservative finite-index bound. These finite
checks support the manuscript; they are not proofs of its infinite or
asymptotic statements. Essential checks use explicit exceptions, so they
remain active when Python is run with `-O`.

## Definitions

The script computes

\[
a_n=(n+1)\log(n+1)-n\log n-1,\qquad
g_0=1,\qquad g_n=\sum_{j=1}^n a_jg_{n-j}.
\]

Here \(\rho\) solves \(\sum_{j\ge1}a_j\rho^j=1\),
\(\gamma=(\sum_{j\ge1}j a_j\rho^j)^{-1}\), and
\(b_n=\gamma\rho^{-n}-g_n\). The computed recurrence uses
\(h_n=\rho^ng_n\) to avoid unnecessarily large intermediate values. The default
precision is \(\lceil0.27N\rceil+100\) decimal digits; enough precision remains
after dominant-term subtraction to diagnose the small residual.

## Output files

| File | Content |
| --- | --- |
| `recurrence.csv` | Terms through the requested maximum index, residuals, normalized residuals, and fixed logarithmic truncations K0–K6. |
| `asymptotic_coefficients.json` | Exact symbolic formulas for c0–c10 and decimal evaluations. |
| `product_convergence.csv` | Selected finite products \(C_N=\prod_{j=1}^N g_j/(\gamma\rho^{-j})\). |
| `finite_differences.csv` | Positive-sign finite differences \((-1)^r\Delta^r b_n\) at selected indices and orders through six. |
| `spectral_comparison.csv` | Independent positive spectral-moment computations from 128-, 256-, and 512-node Gauss–Legendre discretizations. |
| `endpoint_spectral_integral.csv` | Scaled endpoint-density quadrature, resummed algebraic sectors, and large-index diagnostics through \(10^{100}\). |
| `diagnostics.json` | Parameters, library versions, precision comparisons, spectral checks, sensitivity checks, and limitations. |

For fixed logarithmic truncations, `Kj` includes the coefficients
\(c_0,\ldots,c_j\) in
\(n^{-2}\sum_{k=0}^j c_k(\log n)^{-k-2}\).

The resummed columns use

\[
F_k(L)=\int_0^\infty
\frac{y^{k-1}e^{-y}}{(L-\log y-\gamma_E)^2+\pi^2}\,dy,
\qquad L=\log n.
\]

The three successive approximations to \(n^2b_n\) are
\(F_2\), \(F_2+F_3/(2n)\), and
\(F_2+F_3/(2n)+(F_4/12-p_2F_4')/n^2\), with
\(p_2=\zeta'(-1)-1/12\). The prime means differentiation with respect to \(L\).

## Interpretation

The arithmetic, root finding, spectral discretizations, and quadrature are
floating computations. They are not mathematical proofs or interval
certificates. Exact symbolic coefficient identities are distinguished from
their use in an asymptotic formula, whose proof is in the article.

The endpoint integral uses the convergent local series through degree 24,
70 decimal digits, and a scaled integration cutoff of 120. A stronger run
at selected indices uses degree 32, 90 digits, and cutoff 160. Both settings
are recorded. Algebraic-sector errors below the chosen precision are left
unreported instead of being displayed as zero.

The finite logarithmic expansions can be inaccurate at moderate indices and
can become worse when one more term is included. The integral representation
retains those logarithmic effects and is the more accurate finite-index
approximation. The finite products recorded in the data are not certified
values of the infinite product.
