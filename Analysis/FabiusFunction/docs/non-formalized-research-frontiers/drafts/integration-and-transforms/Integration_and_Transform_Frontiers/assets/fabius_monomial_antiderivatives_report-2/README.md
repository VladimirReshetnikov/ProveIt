# Dyadic Primitive Ladders and Mellin-Newton Antiderivatives

> **Archived companion bundle.** The former standalone manuscript is now
> consolidated in `../../Integration_and_Transform_Frontiers.tex`, with the
> rendered report at `../../Integration_and_Transform_Frontiers.pdf`. This
> directory retains its supporting computations and figure.

This archive accompanied the report on antiderivatives of monomially weighted Fabius and
Rvachev functions. The repository audit is pinned to ProveIt commit
`a2541a7ee373c0e297de04424f8921ce881e62b7` (27 August 2026).

## Main files

- `../../Integration_and_Transform_Frontiers.pdf` - rendered consolidated report.
- `../../Integration_and_Transform_Frontiers.tex` - current consolidated source.
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

Compile the report (a TeX Live installation with `latexmk` is recommended):

```bash
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
(cd ../.. && pdflatex -interaction=nonstopmode -halt-on-error Integration_and_Transform_Frontiers.tex)
```

These commands update `../../Integration_and_Transform_Frontiers.pdf`.

The recorded reference run used Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0,
Matplotlib 3.10.8, and pdfTeX 1.40.26. The code is not tied to those exact versions.
