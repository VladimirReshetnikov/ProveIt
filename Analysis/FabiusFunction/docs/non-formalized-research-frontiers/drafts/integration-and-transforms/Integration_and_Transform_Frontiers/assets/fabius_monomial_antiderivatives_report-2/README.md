# Dyadic Primitive Ladders and Mellin-Newton Antiderivatives

> **Consolidation note.** The standalone report source and PDF were absorbed
> into Part III of the
> [consolidated volume](../../Integration_and_Transform_Frontiers.tex). This
> directory now contains only supporting assets; Git history preserves the
> former standalone files.

This archive accompanies the report on antiderivatives of monomially weighted Fabius and
Rvachev functions. The repository audit is pinned to ProveIt commit
`a2541a7ee373c0e297de04424f8921ce881e62b7` (27 August 2026).

## Main files

- `../../Integration_and_Transform_Frontiers.tex` - canonical consolidated source.
- `../../Integration_and_Transform_Frontiers.pdf` - rendered consolidated volume.
- `fabius_integrals_experiments.py` - commented numerical and exact-rational experiments.
- `requirements.txt` - Python dependencies for the experiments.

The generated CSV files contain exact or numerical checks of reciprocal-dyadic values,
finite primitive formulas, shifted Rvachev primitives, complete fractional/negative Newton
series, tail estimates, and inverse-quantile areas. `newton_series_convergence.png` is the
figure included in the report, and `run_summary.txt` records the default-run error maxima.

## Central formulas

For nonnegative integer `p`, positive integer `n`, and `0 <= x <= 1`, the normalized
`n`-fold primitive is

```text
I_0^n[x^p F(x)]
  = sum_{k=0}^p (-1)^k binom(p,k) (n)_k
      2^binom(n+k,2) x^(p-k) F(x/2^(n+k)).
```

For a complex exponent `alpha`, the same expression with an infinite sum and
`binom(alpha,k)` is normally convergent and entire in `alpha`. The inverse-function identity
is

```text
integral_0^y Q(v)^alpha dv
  = y Q(y)^alpha - alpha integral_0^{Q(y)} x^(alpha-1) F(x) dx,
```

where `Q = F^{-1}`. At `alpha = 1` this becomes

```text
integral Q(y) dy = y Q(y) - F(Q(y)/2) + C.
```

## Current Lean crosswalk

The report's repository-novelty audit remains pinned to commit
`a2541a7ee373c0e297de04424f8921ce881e62b7`. The reusable normalized Volterra layer has a
later, focused-build-verified checkpoint at compiled commit `e109088ed`. In
`FabiusFunction.NormalizedVolterra`, writing `J(n,a,f,x)` for the order-`n` normalized
Volterra primitive:

- `normalizedVolterra_affine` proves the division-free forward law
  `J(n,c*a+d,f,c*x+d) = c^n J(n,a,t |-> f(c*t+d),x)` for every real `c`, including zero
  and negative scales, and for order zero. It requires neither integrability nor a complete
  target space.
- `normalizedVolterra_comp_affine` proves the divided inverse law
  `J(n,a,t |-> f(c*t+d),x) = (c^n)^(-1) J(n,c*a+d,f,c*x+d)` under the necessary hypothesis
  `c != 0`.
- `normalizedVolterra_basepoint_shift` proves the local-tail-plus-finite-Taylor-jet formula
  with interval integrability on `a..b` and `b..x`, no ordering of `a,b,x`, and order zero
  included.
- `normalizedVolterra_succ_eq_taylor_of_eq_zero` proves that a positive-order primitive is
  exactly the inherited finite Taylor jet when `f` vanishes on the open unoriented interval
  between `b` and `x`. It needs integrability only on `a..b`; endpoint values and endpoint
  order are irrelevant, including the coincident case `b = x`.

The last declaration formalizes the generic zero-tail polynomial structure. Separately,
`normalizedVolterra_pow_mul_extendedFabius` and
`normalizedVolterra_pow_mul_fabiusReal_of_le_one` formalize the signed-global and bounded
`x <= 1` natural-monomial coefficients. The survival, shifted-up, and exterior piecewise
moment specializations displayed in the report retain their stated paper-proof status.

## Reproduction

Create an environment and install the numerical dependencies:

```bash
python -m venv .venv
. .venv/bin/activate                 # PowerShell: .venv\Scripts\Activate.ps1
python -m pip install -r requirements.txt
```

Regenerate all experimental outputs:

```bash
python fabius_integrals_experiments.py --output-dir .
```

Compile the report with three explicit passes, then remove the generated sidecars:

```bash
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && rm -f *.aux *.log *.out *.toc)
```

The recorded reference run used Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0,
Matplotlib 3.10.8, and pdfTeX 1.40.26. The code is not tied to those exact versions.
