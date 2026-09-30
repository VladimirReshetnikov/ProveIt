# Beyond Finite-Action Folds
## Critical Hahn Transseries, Stable Sector Asymptotics, and Sharp Action Budgets

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

The 25-page article (24 pages as delivered; see the amendments below) studies

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

The delivered checksum ledger `SHA256SUMS.txt` was verified in full on
filing (batch 47) and not kept; the delivered archive remains in the
repository history (see `docs/incoming/README.md`, batch 47 row).

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

On Windows NumPy's `longdouble` is binary64 rather than the 80-bit type of
the recorded Linux run. A rerun there (2026-09-29, on a copy) passed all 80
exact comparisons and reproduced the three tables, `finite_fold.csv` and
`run_summary.txt` byte for byte; the other four CSVs and
`data/verification.json` differ only in the last one to three significant
digits of floating diagnostics (for example the maximum quadrature difference
`2.33935e-12` against the recorded `2.33941e-12`). The exact results and the
75-digit constants agree. `code/verify.py` rewrites every file in `data/`,
so run it on a copy.

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

## Editorial amendments (ProveIt, 2026-09-29)

These changes were made on filing, after the batch-47 delivery. Every change
to the article text is marked in `article.tex` by a comment beginning
`% ed. (2026-09-29)`; visible additions are headed "Editorial note (ProveIt,
2026-09-29)" or, in the bibliography, "[Editorial addition, ProveIt,
2026-09-29.]".

- `article.tex`:
  - an unnumbered `ednote` environment for editorial notes (no numbering
    changes);
  - an editorial note in Section 1.1 naming the moving-fold article's
    `thm:actions` as the finite-action result continued here, and recording
    that the model is the slice `c_j = beta a_j`, `a_j = lambda_j = j` of the
    regularity article's uncited further-research question "Amplitudes,
    general actions, and multiple scales" (whose general type identity is not
    addressed);
  - editorial notes at research Questions 1, 2, 4 and 7 recording what the
    later packages of this series answer: at `alpha = 2`, the
    logarithmic-endpoint and marginal packages (two independent proofs of one
    endpoint theory, constants equal after a change of logarithmic
    normalization; Question 7 answered there, Questions 1 and 2 in part), and
    for the joint limit `alpha_n -> 2` of Question 4 the confluent and
    stable–Gaussian packages (independent, agreeing term by term). The lower
    endpoint `alpha -> 1` stays open, and no answer is marked beyond what was
    checked;
  - four editorial bibliography entries (`ed:lce`, `ed:mct`, `ed:cct`,
    `ed:sge`) for those packages.
- `article.pdf`: rebuilt from the amended source (25 pages; the delivered
  PDF had 24). `BUILD_VALIDATION.json` still describes the delivered build.
- `code/verify.py`: CSV and text outputs are written with LF line endings
  (the CSV writer emitted CRLF on every platform, and `write_text` CRLF on
  Windows). A rerun on a copy gave LF files equal to the earlier Windows
  rerun of the delivered program after removing CRs.
- `README.md`: the retired checksum ledger is no longer listed; the Windows
  `longdouble` behaviour is documented; the page count is updated; this
  section.

### Batch-50 cross-reference notes (ProveIt, 2026-09-29)

Added when batch 50 was filed; marked in the source by `% ed. (2026-09-29)` comments.

- `article.tex`: in the editorial note at Question 1, "For `1<alpha<2` the
  question is open." is replaced: for `1 < alpha < 2` it is answered by
  `../Slowly_Varying_Action_Tails_Critical_Transseries/` (batch 50; scale,
  profile and budget for every slowly varying `l`, with the `Gamma(-alpha)`
  normalization dictionary; a counterexample to the Hahn grid; a convergent
  Lambert chart and an effective-index expansion for `(log j)^m`).
- `article.pdf`: rebuilt (25 pages, unchanged; no errors, undefined
  references, multiply defined labels or duplicate destinations).
