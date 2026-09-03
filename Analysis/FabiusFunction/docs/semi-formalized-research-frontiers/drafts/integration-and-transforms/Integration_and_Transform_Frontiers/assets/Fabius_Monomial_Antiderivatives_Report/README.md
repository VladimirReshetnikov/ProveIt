# Fabius Monomial Antiderivatives and Inverse-Quantile Integrals

> **Consolidation note.** The standalone report source and PDF were absorbed
> into Part II of the
> [consolidated volume](../../Integration_and_Transform_Frontiers.tex). This
> directory now contains only supporting assets; Git history preserves the
> former standalone files.

This archive contains a frontier research report prepared from the recursive
TeX corpus under `Analysis/FabiusFunction/docs` in Vladimir Reshetnikov's
`ProveIt` repository, together with reproducible exact and numerical checks.

The novelty statements in the report are **snapshot-relative**: they mean that the stated formulas were not found in the audited repository snapshot of 27 August 2026. They are not unconditional claims of worldwide priority.

## Current Lean formalization status

The natural-order core of the report is now formalized, in stronger form than
the original statements:

- `FabiusFunction.NormalizedVolterra` defines the literal iterator
  `iteratedPrimitive` and the Cauchy-kernel operator `normalizedVolterra` for
  arbitrary real normed-space-valued inputs, arbitrary base points, oriented
  endpoints, and every natural order, including order zero.
- `iteratedPrimitive_eq_normalizedVolterra` identifies literal repeated
  integration with the normalized kernel for continuous Banach-valued inputs.
  The same module proves the generic finite commutators
  `normalizedVolterra_polynomial` and `normalizedVolterra_monomial`; these need
  only interval integrability of the input.
- The forward affine theorem `normalizedVolterra_affine` has an arbitrary real
  normed target and every real scale `c`, including `c = 0` and negative `c`.
  Its inverse form `normalizedVolterra_comp_affine` assumes exactly `c ≠ 0`.
- `normalizedVolterra_basepoint_shift` assumes only interval integrability on
  the local pieces from `a` to `b` and from `b` to `x`, requires no endpoint
  order, and includes `n = 0`. The positive-order theorem
  `normalizedVolterra_succ_eq_taylor_of_eq_zero` retains only integrability
  from `a` to `b`, assumes that the input vanishes on `uIoo b x`, and is for
  positive order with no endpoint order or endpoint-value condition.
- `FabiusFunction.FabiusAntiderivatives` proves the global signed ladder
  `normalizedVolterra_extendedFabius` and its finite natural-monomial formula
  `normalizedVolterra_pow_mul_extendedFabius` for every real endpoint.
- For the bounded Fabius function, the exact formalized scope is the proved
  initial half-line `x <= 1`, not just `[0,1]`. The declarations are
  `normalizedVolterra_fabiusReal_of_le_one` and
  `normalizedVolterra_pow_mul_fabiusReal_of_le_one`.

The four generic affine/basepoint declarations do not themselves compute
explicit Fabius/up coefficients or assemble the report's piecewise formulas.
They were focused-build verified at compiled checkpoint `e109088ed`.

Everything beyond that natural-order finite core remains a research frontier
in this report: complex powers and their convergence/remainder estimates,
logarithmic and Mellin consequences, fractional primitive order, Rvachev
piecewise and fractional primitives, inverse-Fabius primitives and
asymptotics, and the bounded function's global piecewise continuation for
`x > 1`. The numerical experiments provide checks, not Lean proofs of those
claims.

## Archive contents

- `../../Integration_and_Transform_Frontiers.tex` — canonical consolidated source.
- `../../Integration_and_Transform_Frontiers.pdf` — rendered consolidated volume.
- `experiments.py` — commented, network-free exact and numerical verification code.
- `numerical_results.txt` — full output from the production run.
- `series_convergence.csv` — selected partial sums of the complex-exponent series.
- `README.md` — this file.
- `SHA256SUMS` — checksums for the files above, excluding the checksum file itself.

## Principal results

For the bounded Fabius function `F`, the report proves the zero-based primitive
ladder on the formalized range `x <= 1`

```text
A_n(x) = 2^{n(n-1)/2} F(x/2^n),     A_n'(x) = A_{n-1}(x) (n>=1),     A_0=F.
```

It follows that, for every nonnegative integer `p` and `x <= 1`, a finite
closed form is

```text
∫ x^p F(x) dx
 = Σ_{k=0}^p (-1)^k p!/(p-k)! · 2^{k(k+1)/2}
     · x^{p-k} F(x/2^{k+1}) + C.
```

For every complex exponent `alpha` and `0 < x <= 1`, endpoint flatness upgrades repeated integration by parts to an exact, absolutely and locally uniformly convergent series

```text
∫_0^x t^alpha F(t) dt
 = Σ_{k>=0} (-1)^k alpha^(falling k) · 2^{k(k+1)/2}
     · x^{alpha-k} F(x/2^{k+1}).
```

The report also develops:

- finite moment formulas linked to the repository's dyadic, Bernoulli, Thue–Morse, and q-binomial arithmetic;
- logarithmic weights obtained by differentiation in the complex exponent, with Stirling- and Bell-polynomial coefficients;
- an entire Mellin transform and its probabilistic moment representation;
- primitives of `1-F(x)`, `F(1-x)`, the Rvachev up-function, and the signed global extension;
- branch-sensitive fractional and negative powers for the up-function, and a branch-free global formula for `|x|^alpha up(x)` when `Re(alpha)>-1`;
- the exact inverse-Fabius primitive

```text
∫ J(y) dy = y J(y) - F(J(y)/2) + C,     J=F^{-1},
```

  and a general weighted reduction to nonlinear integrals of powers of `F`;
- a separate critical logarithmic formula at inverse weight `y^{-1}`, a convergence transition at exponent `-1`, a finite Thue–Morse spline limit for the nonlinear remainder, and Lambert-W-controlled endpoint asymptotics;
- conjectures, future research directions, and a Lean formalization roadmap.

## Reproduce the computational checks

Requirements:

- Python 3.10 or newer;
- `mpmath`;
- `numpy`;
- `scipy`.

Run the full calculation in the archive directory:

```bash
python experiments.py --output-dir .
```

Run a faster smoke test with fewer series terms and Sobol points:

```bash
python experiments.py --quick --output-dir ./quick-check
```

The script makes no network requests. It verifies the polynomial primitive identity exactly for `p=0,...,12` using rational arithmetic, checks two equivalent exact moment formulas, evaluates the complex-exponent series at high precision, and independently compares it with scrambled Sobol quasi-Monte Carlo estimates. The simulation is only a cross-check and is not used in the proofs.

## Compile the LaTeX report

The source is self-contained. A typical TeX Live build is:

```bash
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && rm -f *.aux *.log *.out *.toc)
```

The document uses the Libertinus text family when available and falls back to Latin Modern. The supplied PDF was built with TeX Live and has embedded fonts, hyperlinks, a table of contents, and PDF bookmarks.

> **Editorial note (2026-08-28):** the report source (.tex) and compiled PDF listed above were removed from this directory after their content was merged into the volume `Integration_and_Transform_Frontiers.tex`; their SHA-256 hashes remain in the volume provenance section, and git history archives the files. This directory keeps only figures, data, and scripts.
