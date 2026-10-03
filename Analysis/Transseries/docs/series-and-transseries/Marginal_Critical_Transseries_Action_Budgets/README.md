# Marginal Critical Transseries

**Convergent Lambert-W Charts, Universal Cutoff Corrections, and Certified Action Budgets**

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Main model and results

The article studies U_beta(q) = beta sum(a_j q^j exp(j U_beta(q))) with
nonnegative weights, a_1 > 0, and a_j = a/j^3 outside a finite set.
At critical coupling beta_* = 1/sum(j a_j), it proves:

1. A convergent inverse chart around an exact Lambert-W_{-1} core, with
   rational coefficient functions, an explicit geometric remainder, and
   a finite logarithmic generating grid; no finite Puiseux chart exists.
2. An all-orders Gaussian-logarithmic asymptotic expansion for the original
   sector coefficients, uniform in a bounded moving coupling window.
3. The sharp action-budget scale sqrt(n), distinct from the fluctuation
   scale sqrt(n log n), and the limiting retained fraction exp(-1/(2 ell^2)).
4. A finite-prefix-independent first cutoff correction, including a moving
   coupling window, and a two-term expansion of the minimal action budget.
5. A separate explicit finite-n retention inequality based on positive
   coefficient recurrences and an elementary Fourier majorant.
6. A convergent reduced logarithmic chart for finite-action folds, with
   separate algebraic remainder estimates for their drift and curvature.

The article includes ten further research targets and an explicit account
of proof dependencies and formalization boundaries.

## Files

- `Marginal_Critical_Transseries.tex`: standalone editable LaTeX, including references.
- `Marginal_Critical_Transseries.pdf`: compiled 26-page A4 article (25 pages
  as delivered; rebuilt on filing, see the amendments below).
- `code/verify.py`: main exact checks and numerical diagnostics.
- `code/supplementary.py`: general-window and finite-fold checks.
- `data/verification.json`: successful full main run.
- `data/verification_quick.json`: smaller successful main run.
- `data/supplementary.json`: successful supplementary run.
- `notes/PROOF_STATUS.md`: assumptions and verification limits.
- `notes/SOURCE_NOTES.md`: inspected sources and novelty boundaries.
- `notes/BUILD_REPORT.json`: build, layout, and verification summary.
- `build.sh`: three-pass LaTeX build.
- `requirements.txt`: numerical dependency versions used.

The delivered checksum ledger `SHA256SUMS.txt` was verified in full on
filing (batch 48) and not kept; the delivered archive remains in the
repository history (see `docs/incoming/README.md`, batch 48 row).

## Build

Run `sh build.sh` from this directory. A standard TeX Live installation
with pdflatex and the packages in the preamble is required. No external
bibliography processor, repository checkout, network connection, figures,
or private font files are needed to build the article.

## Reproduce the checks

```sh
python -m pip install -r requirements.txt
python code/verify.py
python code/supplementary.py
```

A shorter numerical run is available as `python code/verify.py --quick`;
it writes `data/verification_quick.json` and leaves `data/verification.json`
alone. The full run and `code/supplementary.py` rewrite their JSON files in
place (a rerun on a copy on Windows, 2026-09-29, reproduced all three JSON
files byte for byte). The article's tables are typed into the source and are
not rewritten; `build.sh` overwrites the PDF.
The recorded environment used Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0.
The main run uses 50 decimal working digits; the supplementary run uses 40.

The main run passed 102 finite exact checks; the supplementary run passed 9.
The 111-check total includes coefficient equations whose zero-degree cases
are simple identities; it is a finite diagnostic count, not a count of
independent research theorems. The main numerical program also independently
compares Fourier evaluations with a positive recurrence at n=256.

## Research and verification status

The mathematical results have conventional proofs in the article. No new
Lean formalization, independent peer review, or established global publication
priority is claimed. Classical Lagrange inversion, Lambert inversion, normal
attraction, and extreme-value mechanisms are credited rather than presented
as new discoveries. The proposed contribution is the explicit combined
marginal theory and its correction/certification formulas.

The local inverse chart is convergent. The all-orders sector expansion is
only asserted to be asymptotic. The finite-fold chart is a convergent reduced
chart with a separate finite-M error, not a claim of a convergent unrestricted
joint expansion.

The finite-n inequality is mathematically rigorous. The supplied floating-point
evaluations are NOT outward-rounded interval certificates, and working
precision is not a certified number of accurate output digits. Numerical
checks do not prove infinite-support or uniform asymptotic assertions.

The repository was inspected at the scope described in the article; its full
canonical transseries volume and incoming archives were not exhaustively
audited. No repository files or branches were modified.

## Editorial amendments (ProveIt, 2026-09-29)

These changes were made on filing, after the batch-48 delivery. Every change
to the article text is marked in `Marginal_Critical_Transseries.tex` by a
comment beginning `% ed. (2026-09-29)`; visible additions are headed
"Editorial note (ProveIt, 2026-09-29)" or, in the bibliography, "[Editorial
addition, ProveIt, 2026-09-29.]".

- `Marginal_Critical_Transseries.tex`:
  - an unnumbered `ednote` environment for editorial notes (no numbering
    changes);
  - a scope note after the research-status paragraph: "Certified" in the
    title means the proved inequality of Theorem `thm:finite-certificate`;
    the recorded evaluations use no directed rounding and are not interval
    or proof-assistant certificates;
  - an editorial note in Section 1.1: the logarithmic-endpoint package filed
    beside this one proves the same endpoint core independently (notation
    dictionary; `kappa_1`, `kappa_2` are its `g_1`, `g_2` in another
    logarithmic normalization; the results unique to each);
  - editorial notes at research Question 1 (answered, pending review, by the
    batch-49 stable–Gaussian package in exactly its window and by the
    confluent package at any rate at leading order; they agree term by term)
    and Question 2 (partial progress: log-weighted tails at leading order in
    the logarithmic-endpoint package);
  - the filed location of the companion draft (the critical Hahn package,
    whose Question 4 this article answers at `alpha = 2` without citing it by
    number), and three editorial bibliography entries (`ed:lce`, `ed:cct`,
    `ed:sge`).
- `Marginal_Critical_Transseries.pdf`: rebuilt from the amended source
  (26 pages; the delivered PDF had 25). `notes/BUILD_REPORT.json` still
  describes the delivered build.
- `code/verify.py`, `code/supplementary.py`: JSON outputs are written with LF
  line endings (`write_text` emitted CRLF on Windows).
- `README.md`: the retired checksum ledger is no longer listed; rerun
  behaviour documented; page count updated; this section.
