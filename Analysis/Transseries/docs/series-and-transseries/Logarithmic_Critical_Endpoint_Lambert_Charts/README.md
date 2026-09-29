# The Logarithmic Critical Endpoint

**Convergent Lambert Charts, All-Order Sector Laws, and Sharp Action-Cutoff Corrections**  
Research draft prepared for Vladimir Reshetnikov, 29 September 2026.

## Main content

This 29-page article (28 pages as delivered; see the amendments below) studies the positive countable-action equation

    U_beta(q) = beta * sum_{j>=1} a_j q^j exp(j U_beta(q)),

where `a_j = a/j^3` outside a finite set. It develops an exact convergent
Lambert–analytic critical inverse, an arbitrary-order inverse-logarithmic
sector expansion, a quantitative finite-coupling action-cutoff formula, and
convergent all-order functions for finite-action fold drift and curvature.
A further theorem treats leading inversion and cutoff laws for
`a_j ~ a j^(-3) (log j)^r`, including `r = -1`.

The preceding countable-action manuscript asks for endpoint logarithmic
charts and cutoff laws. This article treats the fixed upper endpoint, not
the full joint limit of its exponent with the sector index. The leading
Gaussian/extreme-scale separation has classical precedents, acknowledged
explicitly through Janson's Example 18.29. The specialized chart and
correction formulas are contributions developed here; worldwide publication
novelty has not been established. No Lean formalization is claimed.

## Files

- `article.tex`: complete editable article with bibliography; uses the four
  included generated table fragments under `data/`.
- `article.pdf`: compiled 29-page PDF (rebuilt on filing).
- `code/verify.py`: exact symbolic checks and numerical diagnostics.
- `data/verification.json`: full results, precision and package versions.
- `data/verification_run.txt`: stdout from the supplied full verification run.
- `data/*_table.tex`: the four reproducible table fragments used by the article.
- `requirements.txt`: dependency versions used for the supplied run.
- `Makefile`: verification, PDF build and auxiliary-file cleanup targets.
- `PROVENANCE.md`: repository snapshot, inspected sources and audit boundaries.
- `BUILD_REPORT.json`: build and validation summary.

The delivered checksum ledger `SHA256SUMS` was verified in full on filing
(batch 48) and not kept; the delivered archive remains in the repository
history (see `docs/incoming/README.md`, batch 48 row).

## Reproduce

The verified environment used Python 3.13.5 and pdfLaTeX from TeX Live.
From this directory:

```sh
python -m pip install -r requirements.txt
python code/verify.py --max-n 65536
make pdf
```

Without `make`, run the following command three times:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The PDF can be rebuilt without running the numerical program: all table
fragments are supplied. No external font files are required or bundled.
For a quicker numerical run, use `--max-n 4096`; it writes its shorter
diagnostic tables into `data/max-n-4096/` (since filing; `--output-dir`
chooses another directory), so the tables the article inputs are not
shortened. The supplied data and PDF use `--max-n 65536`, and that run
rewrites `data/verification.json` and the four table fragments in place, so
run it on a copy.

On Windows (2026-09-29, on a copy) the full run passed, printed output equal
to `data/verification_run.txt`, and reproduced the four tables byte for byte;
`data/verification.json` differed only in the last one to three digits of
floating diagnostics (FFT and NumPy rounding).

## Verification boundary

Exact checks cover the first two nonconstant Lambert chart coefficients,
the finite-fold Y series through degree 7, the drift H series through degree
6, the composed curvature series through degree 5, and the Lagrange identity
through degree 6 in a rational test model. All these checks passed.

The numerical diagnostics are not interval certificates. Fourier coefficient
extraction has a separate rigorous alias bound in exact arithmetic, but its
floating-point roundoff is not globally enclosed. A comparison at index 128
with an independent 80-digit recurrence had relative discrepancy about
6.75e-15 (recorded value 6.75228185529e-15). Root calculations and displayed approximation errors are numerical
diagnostics, not replacements for the article's mathematical proofs.

The large-sector inverse-logarithmic series is asymptotic; convergence is
proved for the local Lambert chart and for the finite-fold generating
functions, not for that large-sector series. Finite-fold approximations may
be exponentiated only under the explicit conditions in Proposition 8.4.

The final PDF has no undefined references, overfull boxes or underfull boxes
in the recorded build. All pages were rendered for visual review; the front
matter was then improved and rechecked. The repository and Library were not
modified.

## Editorial amendments (ProveIt, 2026-09-29)

These changes were made on filing, after the batch-48 delivery. Every change
to the article text is marked in `article.tex` by a comment beginning
`% ed. (2026-09-29)`; visible additions are headed "Editorial note (ProveIt,
2026-09-29)" or, in the bibliography, "[Editorial addition, ProveIt,
2026-09-29.]".

- `article.tex`:
  - an unnumbered `ednote` environment for editorial notes (no numbering
    changes);
  - an editorial note in Section 1.1: the marginal package filed beside this
    one proves the same endpoint core independently (dictionary of the two
    notations; its sector constants are this article's `g_1`, `g_2` in the
    normalization `H_n = log B_n`; the results unique to each);
  - "about 6.76e-15" corrected to "about 6.75e-15" in Section 10 (the
    recorded value is `6.75228185529e-15`);
  - editorial notes at research Question 1 (answered, pending review, by the
    batch-49 stable–Gaussian package in exactly its window and by the
    confluent package at any rate at leading order; they agree term by term)
    and Question 2 (partial progress in the marginal package's finite
    retention inequality; no certified algorithm);
  - "pinned tree" corrected to "pinned commit" (Appendix A and two
    bibliography entries) and "pinned GitHub tree" to "pinned GitHub
    snapshot": the pinned identifier is a commit;
  - the filed location of the preceding article, and three editorial
    bibliography entries (`ed:mct`, `ed:cct`, `ed:sge`).
- `article.pdf`: rebuilt from the amended source (29 pages; the delivered
  PDF had 28). `BUILD_REPORT.json` still describes the delivered build.
- `code/verify.py`: a run with `--max-n` other than the recorded 65536
  writes into `data/max-n-<N>/` (new option `--output-dir`), so it can no
  longer shorten the tables the article inputs; outputs are written with LF
  line endings (`write_text` emitted CRLF on Windows).
- `PROVENANCE.md`: "Pinned tree" corrected to "Pinned commit".
- `README.md`: the rounding corrected; the quick-run and Windows rerun
  behaviour documented; the retired checksum ledger no longer listed; page
  count updated; this section.
