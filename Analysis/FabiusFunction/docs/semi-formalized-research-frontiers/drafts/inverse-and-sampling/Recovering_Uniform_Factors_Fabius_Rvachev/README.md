# Recovering Uniform Factors

## Exact Moment Fibres and Logarithmic Instability Near the Fabius–Rvachev Law

This package contains a self-contained 21-page research article (20 pages
before the editorial notes of 2026-09-29), its LaTeX
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

In the editorial pass after batch 57, a later package of this tree was found
to answer four more of its research questions at the dyadic reference.

- `article.tex`: four further notes, each marked `% ed.`, citing
  `../Anchored_Dyadic_Recovery_Uniform_Spectrum/` (filed 2026-09-29,
  unreviewed). After "Pointwise recovery of the exact dyadic spectrum": the
  anchored modulus on `K` (and on `A_L`, `L > 1`), in total variation or
  Kolmogorov distance, has the exact scale `exp[-Theta(sqrt(log(1/eps)))]`,
  so no Hoelder exponent, yet it is eventually below the pairwise lower
  bound `(eq:modulus-lower)`; its leading constant is bracketed only. After
  "Geometrically separated classes": separation `a_(j+1) <= q a_j` with any
  fixed `q in (1/2, 1)` does not restore a power law at the dyadic
  reference; the pairwise modulus and `q = 1/2` remain open. (The boundary
  case `q = 1/2` was answered later at the dyadic reference, with a
  `Theta(sqrt(epsilon))` modulus; see the editorial amendments of 2026-09-30
  below.) After "Fixed
  leading factors versus the complete sequence": every fixed prefix is
  locally Lipschitz-stable at the dyadic reference on `A_L`, `L >= 1`, with
  `log C_(L,r) <= (log 2) r^2 + O_L(r+1)`; the optimal growth in `r` is open.
  After "Matching statistical upper bounds": only an anchored testing
  version (`exp[Theta(log^2(1/delta))]` samples, confidence sets contracting
  at the dyadic spectrum); a global estimator with a proved risk bound
  remains open. The mathematical text is unchanged.
- `article.pdf`: rebuilt again with `sh build.sh` (MiKTeX 26.2 pdfTeX 1.40.29): 21 pages,
  509,992 bytes; no error, undefined reference, rerun request,
  duplicate destination or overfull box; no Type 3 font; the pages carrying
  the notes were rendered and inspected.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batches 69 and 70 of the repository-level
`docs/incoming/` drop zone (see `docs/incoming/README.md`); the change to the
source is marked `% ed. (2026-09-30)`. The mathematical text is unchanged.

- `article.tex`: a second unnumbered environment `ednotelater` ("Editorial
  note (ProveIt, 2026-09-30)") is defined after `ednote`. Under "Geometrically
  separated classes", after the 2026-09-29 note (which still says that the
  boundary case `q = 1/2` remains open), a note records that
  `../Lacunarity_Boundary_Geometric_Uniform_Spectra/` (filed 2026-09-30,
  batch 68, unreviewed) answers that case at the dyadic reference: on
  `{a in K : a_(j+1) <= a_j/2 for all j}` the anchored modulus at the dyadic
  spectrum is `Theta(sqrt(epsilon))`, a power law, in total variation and in
  Kolmogorov distance, from the fourth-moment certificate
  `sup_j |a_j - 2^(-j)|^2 <= (75/4)(19/675 - E X_a^4)` and explicit
  deleted-factor witnesses, so the stretched-exponential scale for
  `q in (1/2, 1)` does not persist at the boundary. The pairwise modulus on
  separated classes remains open. That package's own editorial note already
  pointed here.
- `article.pdf`: rebuilt with three `pdflatex` passes, as `build.sh` runs
  them (MiKTeX 26.2, pdfTeX 1.40.29): 21 pages, 512,683 bytes; no error,
  undefined reference, rerun request, duplicate destination or overfull box
  (the two underfull boxes of the previous build remain); no Type 3 font;
  the page carrying the note was rendered and inspected.
- `README.md`: the parenthesis after the 2026-09-29 bullet on
  "Geometrically separated classes", and this section.
