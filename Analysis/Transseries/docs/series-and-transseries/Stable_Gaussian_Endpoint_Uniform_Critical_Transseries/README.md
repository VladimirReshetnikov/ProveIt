# Through the Stable–Gaussian Endpoint
## Uniform critical transseries, prefix-independent cutoff corrections, and conditional extremes

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

The 21-page article (20 pages as delivered; see the amendments below) addresses the explicit bounded-window endpoint question
in the companion *Marginal Critical Transseries* manuscript. It studies

    U(q) = sum_{j>=1} w_j q^j exp(j U(q)),
    sum_{j>=1} j w_j = 1,
    w_j = c_epsilon j^(-3+epsilon) outside a finite prefix,
    |epsilon| log n <= K.

Weights are nonnegative, the first weight is positive, and the finite-prefix
family is analytic in the moving parameter. Both signs of epsilon are allowed.
The article states every uniformity condition and uses the original weights
when truncating actions; retained weights are not renormalized.

## Results

Theorem 4.1 proves a two-term uniform critical inverse. Theorem 4.2 constructs
a convergent analytic correction about a desingularized core, with a geometric
truncation bound in Appendix A. Theorem 6.2 proves a uniform lattice local limit
and the first central coefficient correction. Theorem 7.3 gives the uniform
first cutoff correction, including cancellation of finite-prefix moments.
Corollaries 7.5 and 8.1 give the exact lossless-cutoff criterion and a two-term
minimal action budget. Theorem 9.1 proves conditional convergence of large
actions to a Poisson point process. Section 10.2 gives a finite-variance-side
normalization phenomenon. Section 13 proposes eight further research targets.

## Contents

- `article.pdf`: compiled, visually inspected 21-page A4 article (rebuilt on
  filing).
- `article.tex`: self-contained LaTeX source, including tables and bibliography.
- `code/verify.py`: exact algebra and numerical reproduction program.
- `data/recurrence.csv`: 18 positive-recurrence diagnostics.
- `data/large_n.csv`: 9 large-order Fourier diagnostics.
- `data/inverse.csv`: 9 critical-inverse diagnostics.
- `data/verification.json`: exact checks and numerical environment record.
- `data/run_summary.txt`: output of the executed verification run (since
  filing written by `code/verify.py` itself, with the same content).
- `SOURCES.md`: repository snapshot, inspection scope, and primary references.
- `requirements.txt`, `Makefile`: dependencies and build commands.
- `BUILD_VALIDATION.json`: compilation and rendering checks.

The delivered checksum ledger `SHA256SUMS.txt` was verified in full on
filing (batch 49) and not kept; the delivered archive remains in the
repository history (see `docs/incoming/README.md`, batch 49 row).

## Build the PDF

A TeX Live installation with the packages named in `article.tex` suffices.
No custom font files or external images are required. All tables are in the
source; compiling does not require running the numerical program.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `make pdf` where Make is available.

## Reproduce the computations

```sh
python -m pip install -r requirements.txt
python code/verify.py --max-n 4096
```

This regenerates the CSV and JSON files and `data/run_summary.txt` (the
delivered recipe redirected standard output into that file, which truncated
it when the run failed; since filing the script writes it itself, after a
successful run). It does not automatically rewrite the displayed tables in
the LaTeX source. A smaller portable run is:

```sh
python code/verify.py --max-n 512
```

Since filing, a run with `--max-n` other than the recorded 4096 writes into
`data/max-n-<N>/` (or into `--output-dir DIR`), so it cannot replace the
recorded 18-case data with a 6-case run.

The recorded run used Python 3.13.5 and the pinned package versions.
Constants use 75-digit mpmath evaluation; recurrence uses NumPy long double;
Fourier quadrature uses ordinary double precision. On platforms where
`longdouble` has a narrow exponent range (including some Windows builds),
the default initial Poisson probability can underflow. The program reports
that failure; use `--max-n 512` for the small recurrence cross-checks. The
large-order cases use Fourier integrals, not arrays with 10^32 coefficients.

On Windows (2026-09-29, on a copy) the default run stopped with that
underflow error before writing anything, and the recorded data were left
intact. The `--max-n 512` run passed the 17 exact checks; its outputs equal
those of an earlier Windows run of the delivered program (up to line
endings), and its maximum recurrence/Fourier discrepancy was 4.27e-14. The
recorded 4096 run could not be reproduced there.

Seventeen exact symbolic checks passed. Six independent recurrence/Fourier
cross-check cases had maximum absolute discrepancy
3.3306690738754696e-16 across the tested ratios and normalized probabilities.
This agreement is a diagnostic, not an error enclosure or a proof.

## Mathematical and novelty boundaries

The article gives conventional proofs for the stated family. No result from
the companion manuscript is needed as a proof premise. The classical
Lagrange/Poisson mechanism, fixed-index limits, and general heavy-tail
truncation concepts are credited to prior work. The proposed contribution is
the uniform moving-index theory and its explicit correction formulas.
Global publication priority, independent peer review, and Lean formalization
are not claimed. Numerical results are not interval certificates. No files
in the ProveIt repository were modified.

## Editorial amendments (ProveIt, 2026-09-29)

These changes were made on filing, after the batch-49 delivery. Every change
to the article text is marked in `article.tex` by a comment beginning
`% ed. (2026-09-29)`; visible additions are headed "Editorial note (ProveIt,
2026-09-29)" or, in the bibliography, "[Editorial addition, ProveIt,
2026-09-29.]".

- `article.tex`:
  - an unnumbered `ednote` environment for editorial notes (no numbering
    changes);
  - an editorial note in Section 1.1: the marginal companion is now filed;
    the same question is Question 1 of the logarithmic-endpoint package,
    which this article did not see; the confluent package filed with this
    one answers it independently at leading order for every rate; the two
    agree term by term (scales, window forms, minimal budget, profile,
    conditioned Poisson limit), this article goes one order further in its
    window, and at `eps = 0` its first cutoff correction is that of the
    marginal and logarithmic-endpoint packages;
  - the filed location of the marginal companion in its bibliography entry,
    and two editorial bibliography entries (`ed:lce`, `ed:cct`);
  - the title page no longer sets a hyperref page anchor, which removes a
    duplicate `page.1` destination warning.
- `article.pdf`: rebuilt from the amended source (21 pages; the delivered
  PDF had 20). `BUILD_VALIDATION.json` still describes the delivered build.
- `code/verify.py`: CSV and JSON outputs are written with LF line endings
  (the CSV writer emitted CRLF on every platform, `write_text` CRLF on
  Windows); a run with `--max-n` other than 4096 writes into
  `data/max-n-<N>/`; new option `--output-dir`; the script writes
  `run_summary.txt` itself after a successful run. The summary format was
  checked against the recorded `data/run_summary.txt`: rebuilt from the
  recorded JSON and CSV it is byte-identical.
- `Makefile`: the `verify` target no longer redirects standard output over
  `data/run_summary.txt`.
- `README.md`: the retired checksum ledger is no longer listed; the rerun
  recipe and the Windows rerun documented; page count updated; this section.
