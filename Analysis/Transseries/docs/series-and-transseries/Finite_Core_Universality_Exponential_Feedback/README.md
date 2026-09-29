# Finite-Core Universality and Sharp Large Order
## Countable exponential-feedback transseries

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

The 26-page article studies the formal equation

    U(q) = sum_{j>=1} q^j exp(a j^p U(q)),  a>0, p>1,

and nonnegative perturbations of finitely many initial weights and slopes,
with the first primitive weight fixed at one.

## Main results

The coefficient contribution of exactly one action above a finite analytic
core of size M is asymptotic to the full coefficient if and only if
M(p-1)>1. At or below the boundary its relative contribution tends to zero.
The paper gives a full multiplicative saddle formula, conditional local
Gaussian fluctuations and an unconditional central limit theorem, an explicit
quadratic correction, a coefficient-ratio and least-formal-term law, and sharp
formal inverse asymptotics in the superquadratic range p>2.

All proofs are conventional mathematics. No Lean verification or exhaustive
originality/priority certification is claimed. The proposed quadratic inverse
equivalent is explicitly a conjecture, not one of the proved results.

## Files

- `article.pdf` and `article.tex`: compiled article and self-contained source.
- `code/verify_exact.py`: standard-library exact arithmetic, independent
  partition and marking comparisons, and inverse-composition residual checks.
- `code/diagnostics.py`: NumPy/SciPy positive log recurrence and finite-core
  nonlinear saddle calculations.
- `code/report_tables.py`: table generation and exact-versus-floating cross-checks.
- `data/`: exact integer-normalized CSV coefficients, numerical CSV/NPZ data,
  JSON reports, and generated table rows.
- `PROOF_STATUS.md`: boundaries and proof dependencies.
- `SOURCES.md`: repository provenance and primary literature.
- `requirements.txt`, `Makefile`: reproduction aids.

## Build the article

The source embeds its bibliography and all tables, so it compiles without
running Python or downloading repository files. Use a TeX installation with
standard mathematical packages, Latin Modern, xurl, hyperref and bookmark.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

A third pass can be used if TeX reports changed cross-references. `make` runs
three passes. No external font files are included or required by the package.

## Reproduce the calculations

Use Python 3.10 or later. Exact calculations need only the standard library.

```sh
python code/verify_exact.py --order 300
python -m pip install -r requirements.txt
python code/diagnostics.py --order 1000 --powers 2 3
python code/report_tables.py
```

The numerical driver is primarily tested on p=2 and p=3. For p close to one,
its automatically selected core can become large, and a moderate n may lie
outside the small-branch regime. Such a solver failure is not a contradiction
of the fixed-parameter asymptotic theorem.

## Recorded verification

For a=1 and p=2,3, exact coefficients and inverse coefficients were computed
through degree 300. All 36 independent partition checks, 96 independent
one-tail marking checks, and 598 inverse-composition residual checks passed.
The residual checks are not a separate independent algorithm for inversion.

Positive log-domain coefficients were computed through degree 1,000.
Agreement with the exact coefficients through degree 300 was within 9.1e-13
in absolute log discrepancy in the recorded run. These are floating-point
diagnostics, not interval certificates. Numerical asymptotic agreement does
not prove the article's limit theorems.

The exact CSV columns contain **n! times** ordinary coefficients. Divide by
n! to recover u_n or v_n. Negative inverse values are retained with their signs.

No ProveIt repository file, branch, issue, or pull request was modified.
