# Complete small-argument asymptotics of the inverse Fabius function

This archive accompanies the report prepared on 28 August 2026 from the
`VladimirReshetnikov/ProveIt` repository snapshot
`ad82c27ffc6f90b3406f46c130c86d3cb83c6225`.

## Files

- `inverse_fabius_complete_asymptotics.tex` — complete LaTeX source.
- `inverse_fabius_complete_asymptotics.pdf` — rendered 23-page report.
- `inverse_fabius_experiments.py` — fully commented symbolic/numerical
  verification and coefficient-generation program.
- `generated_coefficients.tex` — machine-generated saddle coefficients through
  the requested generation order.
- `verification_output.txt` — exact symbolic checks and high-precision numerical
  residuals from the program.
- `psi_periodic.pdf` — vector plot of the Gamma-zeta periodic fluctuation.
- `dyadic_tail_convergence.pdf` — vector plot of convergence of the exact
  2-adically weighted exponential expansion.
- `requirements.txt` — Python dependencies used for reproduction.
- `SHA256SUMS` — checksums of the release files.

## Main results developed in the report

The report imports the repository's existing all-orders forward endpoint
expansion and its phase-aware recursive inverse construction, then develops
several coefficient-level extensions:

1. A nonrecursive bivariate Lagrange--Buermann coefficient extractor for every
   inverse Lambert-phase coefficient `d_n`.
2. A direct partial-Bell-polynomial formula for every multiplicative inverse
   coefficient `g_n`.
3. The universal highest-logarithm law

       [ (log rho)^n ] g_n = 1 / (2^n n!).

4. A finite constrained-partition formula for every Gaussian/Bromwich saddle
   coefficient, including the CDF denominator.
5. An all-orders operator calculus for logarithmic and ordinary derivatives of
   the inverse quantile.
6. The exact 2-adic identity

       -sum_{k>=0} log(1-exp(-2^k t))
       = sum_{n>=1} ((2^(v_2(n)+1)-1)/n) exp(-n t),

   its Mahler equation, Dirichlet series, Mellin transform, and exact correction
   to the saddle map.
7. A beyond-all-orders program in which the ultraflat sectors retain the exact
   saddle coordinate `q_star`; replacing it by the algebraic phase inside
   `exp(-2^q_star)` changes the exponential scale.

Claims marked “new” are new relative to the inspected repository snapshot; the
report does not claim global publication priority.

## Reproduction

Python 3.11 or newer is recommended.  The report was generated with Python
3.13.5, SymPy 1.14.0, mpmath 1.3.0, NumPy 2.3.5, Matplotlib 3.10.8, and a
TeX Live 2025 development installation.

Create an environment and regenerate the calculations and figures:

```bash
python -m venv .venv
. .venv/bin/activate                 # Windows PowerShell: .venv\\Scripts\\Activate.ps1
python -m pip install -r requirements.txt
python inverse_fabius_experiments.py --max-saddle-order 3
```

Compile the report:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  inverse_fabius_complete_asymptotics.tex
```

The symbolic generator may be run at a higher fixed saddle order by increasing
`--max-saddle-order`; expression growth, rather than numerical conditioning, is
the practical limitation.

## Verification summary

The archived run verifies the first three generalized Lagrange--Buermann
coefficients exactly in SymPy.  It also checks the exact Laplace decomposition,
the 2-adic product/series identity, the Dirichlet-series identity, and the
Mellin bridge at high precision.  The PDF was compiled with resolved references
and visually inspected after rendering all 23 pages at 180 dpi.
