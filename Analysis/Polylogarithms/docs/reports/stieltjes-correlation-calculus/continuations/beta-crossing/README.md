# Beta Mixtures Across Integer Twists

**Finite spectral corrections, harmonic logarithmic moments, and
Stieltjes–polylogarithm primitives**

Research continuation prepared for the ProveIt project, October 10, 2026.
The article is 24 pages and includes complete proofs, nine proposed
research directions, and a reproducibility appendix.

## Read first

`article.pdf` is the reading copy; `article.tex` is its complete,
self-contained LaTeX source. No external figures or local font files are
required. The mathematical core is also supplied as an integration
fragment under `integration/`.

The central extension is relative to the inspected manuscript section
`07-mixed-twist-identities.tex`. For arbitrary nonintegral real twists
and positive-real-part individual orders whose sum is a positive integer,
the affine finite-part Dirichlet mixture differs from the convolution by
an explicit finite Fourier polynomial. The formula includes every crossed
mode and the zero mode. Its balanced order derivatives and their
chamberwise kernel/rank are proved at every order and depth.

The scalar specialization gives a Gamma–cotangent generator, all ordinary
centered-logarithm moments at integer endpoint orders, and finite
classical-polylogarithm primitives. A separate logistic Mellin calculation
gives finite Hurwitz reductions, explicit polygamma formulas, all
logarithmic Mellin finite parts, and Stieltjes antiderivative ladders.

## What the package does not claim

The existing common-interval theorem is correct as written. The new
formula is a continuation, not an allegation that this theorem is wrong.
The article rejects three unsafe extensions/normalization shortcuts with
explicit counterexamples. It does not prove S6 or the revised S8, does not
claim arithmetic independence, and does not claim global literature
priority. Several ingredients are classical and are identified as such.

The targeted chapter was read at commit
`446dca9bd65c20e409d1d2561d4ffad408103e2a`.
Other source reads and the incoming listing have their separate evidence
scope in `provenance/sources.json`. Six incoming ZIP archives were listed
but their binary contents were not opened. This is not an exhaustive audit
or a claim of complete deduplication against those packages.

The mathematical proofs have not received independent peer review or
proof-assistant verification. No GitHub files were modified.

## Reproduce the calculations

The recorded environment was Python 3.13.5, SymPy 1.14.0 and mpmath 1.3.0.
Use Python 3.10 or newer; minor platform/precision variations can change
floating-point residuals.

```sh
python -m pip install -r verification/requirements.txt
python verification/check_exact.py
python verification/check_numeric.py --dps 65
```

The exact script checks 508 finite assertions, including three expected
rejections of uncorrected formulas. The numerical script performs 94
comparisons at 65 decimal digits. Both scripts stop on a failed assertion
and write receipts beside themselves. Existing receipts record the run
made for this delivery. A rerun overwrites those two receipts; preserve a
copy beforehand when comparing runs.

All recorded checks passed. The largest recorded scaled numerical
residual was approximately `1.59e-37`, in the first ordinary inverse-log
integral. This is a floating-point diagnostic, not a certified error
bound. The scripts use explicit Taylor subtraction and finite local
Taylor approximations to avoid cancellation; numerical zeros do not prove
exact equality. The all-index proofs are in the article.

## Build the PDF

A standard TeX installation providing pdfLaTeX and the packages listed in
the source is sufficient. LaTeXmk handles references automatically:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Without LaTeXmk, run `pdflatex -interaction=nonstopmode -halt-on-error
article.tex` three times. The PDF metadata can differ between builds.
For convenience, `Makefile` provides `pdf`, `exact`, `numeric`, `check`,
and `clean` targets. `make clean` removes only TeX build by-products, not
the final PDF or mathematical receipts.

## Verify the distributed files

From the extracted package directory, run `sha256sum -c SHA256SUMS` where
that command is available. Rebuilding the PDF or overwriting verification
receipts changes the corresponding hashes; preserve the original package
when comparing reruns.

## Package map

- `article.tex`, `article.pdf`: complete article and compiled reading copy.
- `integration/`: shared core, small preamble fragment, bibliography
  fragment, and proposed insertion instructions.
- `verification/`: two scripts, pinned Python dependencies, exact and
  numerical receipts, and an artifact inspection record.
- `provenance/`: observed source references and per-theorem status ledger.
- `SHA256SUMS`: checksums for distributed files, excluding itself.

The integration core is generated from the marked region of `article.tex`
by `integration/extract_core.py`. Its bibliography entries are also
extracted from the standalone article, so proof text need not be manually
maintained in two places. Label names start with `bc:`; helper macro names
start with `bc`. See `integration/PROPOSED_INTEGRATION.md` before adding it
to the manuscript.
