# Recovering Uniform Factors

## Exact Moment Fibres and Logarithmic Instability Near the Fabius–Rvachev Law

This package contains a self-contained 21-page research article (20 pages
before the editorial note of 2026-09-29), its LaTeX
source, exact-arithmetic verification code, and the output of a completed run.
It was prepared in response to a request to develop a research extension of
Vladimir Reshetnikov's ProveIt repository.

## Main results

For independent uniforms U_j on [-1,1], write X_a = sum_j a_j U_j, with a a
nonnegative decreasing summable spectrum. The dyadic spectrum is a_j = 2^(-j).

* For any M, a nonconstant analytic curve through the dyadic spectrum preserves
  exact support [-1,1] and all moments through degree 2M+1, while its next even
  cumulant changes.
* Explicit Chebyshev pairs have a witnessing ordered-coordinate gap at least
  1/(48 n^2) and total-variation distance at most 40 n (6/7)^(2n-1).
* A common normalization fixes variance at 1/9, retains support inside [-3,3],
  and bounds every density derivative uniformly. The gap bound becomes
  1/(96 n^2). Both laws approach the Fabius–Rvachev law in total variation.
* These pairs rule out every pairwise local Hölder inverse estimate and give
  an inverse-modulus lower bound of logarithmic-squared order.
* For N independent observations the minimax expected sup-coordinate loss is
  at least 1/(768 ceil(10 log(100 N))^2) over the stated class. The same lower
  bound holds locally for sufficiently large N.

Full-law identifiability is established background, attributed in the article
to Billey and Swanson. The explicit quantitative construction is presented as
a proposed contribution, not as a certified priority claim or a solution of a
named published open conjecture.

## Contents

- `article.pdf`: compiled article.
- `article.tex`: standalone LaTeX source; table data are embedded.
- `code/verify.py`: exact polynomial/cumulant/rank checks and numerical diagnostics.
- `data/verification.json`: structured results and software versions.
- `data/verification.txt`: human-readable run summary.
- `data/table_rows.tex`: generated numerical table rows.
- `data/pdf_review.txt`: PDF rendering and build checks.
- `SOURCES.md`: provenance and literature boundary.
- `STATUS.md`: precise claim and verification limitations.
- `requirements.txt`: versions used in the recorded verification run.
- `build.sh`: rebuild the PDF from LaTeX.

## Reproduce the checks

Python 3.10 or newer is recommended. The recorded run used Python 3.13.5,
SymPy 1.14.0, and mpmath 1.3.0.

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

The script can be run from any working directory. It writes its output to
`data/`. It does not use the network. An assertion failure terminates the run.
The numerical tests use 90 decimal digits but are not interval certificates.

The completed run passed 6,320 exact power-sum equalities, 158 exact first
defects, 39 exact cumulant defects, eight rank and eight determinant cases,
the explicit analytic-curve identities, and the diagnostics listed in the
article. Finite checks do not replace the all-n proofs.

## Rebuild the PDF

A standard TeX Live installation with pdfLaTeX and the packages listed in the
source is sufficient. No bibliography processor, external figures, font
files, or downloaded source documents are required.

```sh
sh build.sh
```

Alternatively run `pdflatex -interaction=nonstopmode -halt-on-error article.tex`
three times. The PDF can be compiled from `article.tex` alone. Regenerating
`data/table_rows.tex` does not automatically edit the embedded table; if the
construction is changed, keep the table block in `article.tex` synchronized.

## Mathematical boundaries

The no-Hölder statement is pairwise on every neighborhood, not pointwise
against the exact dyadic parameter. The logarithmic exponent is a lower-bound
exponent, not a proved optimum. The explicit TV-small pairs have a common
support containment, not exact support endpoints ±1; the separate analytic
moment-fibre theorem preserves those exact endpoints. No estimator achieving
the lower rate is claimed. The article is unrefereed and no Lean formalization
is supplied.

## Editorial amendments (ProveIt, 2026-09-29)

In the editorial pass after batch 54 of the repository-level `docs/incoming/`
drop zone (see `docs/incoming/README.md`), a later package of this tree was
found to take up one of its research questions. The article gains reciprocal notes; its
mathematical text is unchanged.

- `article.tex`: an unnumbered environment `ednote` ("Editorial note
  (ProveIt, 2026-09-29)") is defined after the last theorem style.
- `article.tex`: after the research question "Gaussian components and
  square-summable spectra", a note records that
  `../Gaussian_Dust_Christoffel_Recovery_Uniform_Factors/` (filed
  2026-09-29, unreviewed) answers it for the Gaussian-variance functional,
  in a model with a known smooth compactly supported background: exact
  minimax risk `V/2` without a tail restriction, and uniform consistency on
  a compact class exactly when its squared-scale tails vanish uniformly.
  Quantitative stability of the scales themselves is not treated there. The
  note is marked `% ed.`.
- `article.pdf`: rebuilt with `sh build.sh` (three pdflatex passes) (MiKTeX pdfTeX): 21 pages (20 before; the note adds one), 505,903
  bytes; no error, undefined reference, rerun request, duplicate
  destination or overfull box; no Type 3 font.
  `data/pdf_review.txt` is the delivered record of the 20-page build.
