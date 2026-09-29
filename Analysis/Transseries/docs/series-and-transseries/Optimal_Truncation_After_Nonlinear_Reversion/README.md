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
- `BUILD_RECEIPT.md`, `environment.json`, `SHA256SUMS`: build/verification receipt,
  executed environment, and package-file checksums.
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

Run from this directory. The scripts regenerate the recorded data files. The
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
