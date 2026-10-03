# Optimal Truncation after Nonlinear Reversion

**A sharp cutoff-transfer theorem and the inverse harmonic function**  
Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Read first

`article.pdf` is the 22-page article; `article.tex` is its standalone editable source.
The central application answers the bounded-offset sharp-remainder part of the
ProveIt predecessor's explicitly stated `prob:direct`. It does not establish a
global enveloping theorem for every argument and every truncation order.

The main general result is Theorem 4.1: a finite-diagonal formula for the difference
between the inverse of a factorially truncated logarithmic correction and the
corresponding direct inverse partial sum. Its application is Theorem 6.1, followed
by eventual local enveloping (Corollary 7.1) and all-orders corrected adjacent
averaging (Theorem 7.2). Section 11 proposes ten further research projects.

The conventional proofs are in the article. The programs provide finite symbolic,
numerical, and exact-rational checks; none is a Lean formalization or independent
refereeing. Global priority has not been established by the targeted search.

## Files

- `article.tex`, `article.pdf`: source and compiled article.
- `verify.py`, `results.csv`, `verification.log`: 312-digit numerical checks through
  inverse coefficient 241, including several bounded offsets. These are not
  interval computations.
- `exact_checks.py`, `exact_certificates.json`, `exact_checks.log`: standard-library
  rational arithmetic. The formal inverse residual vanishes through degree 12;
  six shifted-digamma certificates enclose direct or midpoint errors at selected
  rational arguments. Decimal endpoints are rounded outward by integer arithmetic.
- `derive_coefficients.py`, `symbolic_results.txt`, `symbolic_checks.log`: symbolic
  gamma-moment, transport, cutoff, and corrected-weight calculations and assertions.
- `SOURCE_NOTES.md`: exact repository provenance and limitations.
- `BUILD_RECEIPT.md`, `environment.json`: build/verification receipt and executed
  environment. The receipt describes the delivered 22-page build.
- The delivered checksum ledger was verified in full on filing (batch 48) and not
  kept; the delivered archive remains in the repository history (see
  `docs/incoming/README.md`, batch 48 row).
- `build.sh`, `requirements.txt`: local rebuilding and Python dependencies.

## Build the PDF

Use a TeX Live installation with the packages loaded by `article.tex`, including
newtx, mathtools, amsthm, microtype, xurl, hyperref, and cleveref. No external figures,
repository files, or downloaded font files are required in this archive.

On a POSIX system:

```sh
sh build.sh
```

On any system with `pdflatex` on PATH, the equivalent commands are:

```text
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

## Rerun the checks

Python 3.10 or later is suitable for the type-annotation syntax. The exact-rational
program has no third-party dependencies. The other programs require mpmath and
SymPy; tested versions are pinned in `requirements.txt`.

```sh
python -m pip install -r requirements.txt
python exact_checks.py
python derive_coefficients.py
python verify.py --max-order 240 --output results.csv
```

Run from this directory. The scripts regenerate the recorded data files
(`exact_certificates.json`, `symbolic_results.txt`, `results.csv`), so run them on
a copy to compare. The three `.log` files are their recorded standard output; no
script writes them. The
numerical program prints its working precision, selected scaled residuals, and
elapsed time. Its timing varies with the environment. The exact certificates are
large fractions by design, not estimates reconstructed from floating-point values.

## Scope of the result

The sharp direct error is uniform when `M + 1 - pi*X` remains in a fixed compact
set. Every all-orders assertion means every *fixed* requested amplitude order; it
does not assert uniformity when that order grows with X. Corrected averaging
reduces the algebraic amplitude of exp(-2*pi*X), not its exponential action.
The article explicitly separates the new cutoff-transfer contribution from the
classical inverse coefficients, Binet identities, and the predecessor's known
forward-truncation inverse result.

No repository files were changed.

## Editorial amendments (ProveIt, 2026-09-29)

Made in place after filing (batch 48 of `docs/incoming/README.md`). The author's
text is otherwise unchanged; every change to the article source is preceded by a
`% ed. (2026-09-29)` comment, and no label was renamed or theorem renumbered.

- `article.tex`: three visible "Editorial note (ProveIt, 2026-09-29)" blocks. In
  Section 1.1: the article was written at its pinned reference before two other
  answers to the same `prob:direct` were filed
  (`../Direct_Optimal_Truncation_Inverse_Harmonic/` `thm:sharp`,
  `../Inverse_Digamma_Spectral_Representation/` `thm:optimal`), so its "we resolve"
  (abstract, status line, Section 1) is a third, independent resolution. After the
  proof of `thm:direct`: `D_1`, `D_2`, the `π/6` difference, the half law and the
  order guide `σ = 3/4` agree with those articles term by term; their enveloping
  theorems are stronger than `cor:enveloping`; what is new here is listed. In the
  provenance appendix: the gap was resolved twice before, and their enveloping
  theorems partly answer research question 1. The abstract and status line are
  unchanged (a comment in the abstract points to the notes). The title page no
  longer carries a PDF page anchor (`\hypersetup{pageanchor=false}`), which
  removes a pre-existing duplicate-destination warning.
- `article.pdf`: rebuilt from the amended source with `latexmk -pdf`; 23 pages (the
  delivered PDF had 22), no errors, undefined references, multiply defined labels
  or duplicate destinations.
- `verify.py` (CSV writer with `lineterminator='\n'`), `exact_checks.py`,
  `derive_coefficients.py`: write LF on every platform. A rerun on a copy (SymPy
  1.14.0, mpmath 1.3.0) reproduced `results.csv`, `exact_certificates.json` and
  `symbolic_results.txt` byte for byte; the standard output equals the three
  `.log` files except the two timing lines of `verification.log`.
- Caveat recorded on filing: `derive_coefficients.py` hard-codes the second cutoff
  coefficient `σ²/6 − σ/4 + 25/144` and derives `D_2` from it, and its independent
  check covers only one diagonal of the cancellation claimed in the proof of
  `thm:direct`. The term-by-term agreement of `D_2` with the two independent
  articles closes that gap.
- This README: the checksum-ledger entry, the receipt description and the
  paragraph on what the scripts overwrite.
