# Beyond Finite-Action Folds
## Critical Hahn Transseries, Stable Sector Asymptotics, and Sharp Action Budgets

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

The 24-page article studies

    U_beta(q) = beta * sum_{j>=1} a_j q^j exp(j U_beta(q)),
    a_j = a / j^(1+alpha) outside a finite set, 1 < alpha < 2,

with nonnegative weights and a_1 > 0. It develops a countable-action,
nonanalytic-boundary extension of the ProveIt transseries inversion program.

## Principal results

- Theorems 3.1 and 3.3: a convergent critical Hahn inverse, geometric
  truncation control, and a closed multi-index coefficient formula.
  Corollary 3.4 gives the exact finite-ramification criterion.
- Theorem 5.2: an arbitrary-order stable-density expansion, with a uniform
  additive remainder. Theorem 6.1 proves an exact Hahn/Fourier coefficient
  identity and an arithmetic cancellation rule.
- Theorems 7.2 and 7.3: the joint coupling/action-cutoff profile and the
  necessary-and-sufficient condition M_n / n^(1/alpha) -> infinity for
  preservation of the n-th coefficient at criticality.
- Theorems 8.1 and 8.2: explicit finite-fold critical-value and curvature
  drift, and a triangular-array Gaussian coefficient law below the
  critical cutoff scale.

There are eleven further research topics, a staged formalization plan,
and an explicit source/proof-dependency audit.

## Files

- `article.pdf`: compiled article.
- `article.tex`: LaTeX source, including the bibliography.
- `data/*_table.tex`: three generated tables used by the source.
- `code/verify.py`: exact checks and numerical reproduction program.
- `data/*.csv`: numerical diagnostics.
- `data/verification.json`: exact checks, constants, and numerical run metadata.
- `data/run_summary.txt`: compact record of the executed numerical run.
- `SOURCES.md`: repository snapshot, inspected scope, and literature provenance.
- `BUILD_VALIDATION.json`: build and PDF checks.
- `requirements.txt`, `Makefile`: reproducible dependencies and build commands.
- `SHA256SUMS.txt`: checksums for the packaged files other than itself.

## Build

The recorded run used Python 3.13.5 and the dependency versions in
`requirements.txt`. A TeX Live installation with the packages named in
`article.tex` is sufficient; there are no custom fonts or external images.

```sh
python -m pip install -r requirements.txt
python code/verify.py --max-n 4096
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The stored tables permit compilation without rerunning the computation.
`make pdf` compiles and `make verify` regenerates the data.

The default probability recurrence uses NumPy long double. On systems where
that type has a narrow exponent range, the script automatically falls back
to the slower arbitrary-precision recurrence if its initial probability
underflows. The portable fallback was cross-checked at n=64; its relative
difference from the recorded-platform recurrence was below 2.4e-18.

## Evidence and boundaries

Eighty exact comparisons passed. The numerical examples use 75-digit
constants, positive probability recurrences through target n=4096, and
non-certified Fourier quadrature. The equations are proved conventionally
in the article; these computations are not Lean proofs or interval
certificates. The local Hahn series is proved convergent, whereas the
large-sector expansion is only asserted to arbitrary finite order.

The article explicitly credits classical simply generated tree/stable-limit
and heavy-tail truncation theory. Global novelty and publication priority
for the combined model-specific results have not been certified. The
repository audit covers the listed sources, not the full canonical volume
or the subsequent incoming archive batch. No repository files were changed.
