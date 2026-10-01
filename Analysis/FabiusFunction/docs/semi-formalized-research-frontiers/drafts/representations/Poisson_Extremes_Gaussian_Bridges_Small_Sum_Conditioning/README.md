# Poisson Extremes and Gaussian Bridges under Small-Sum Conditioning

Research manuscript prepared for Vladimir Reshetnikov, 30 September 2026.

## Main contents

`article.pdf` is the compiled article; `article.tex` is its self-contained
LaTeX source with an embedded bibliography. No external figures or bibliography
files are required. `CLAIM_STATUS.md` separates the proved statements, existing
background, numerical diagnostics, and unresolved questions.

The article develops three main results:

1. For weights j^(-p), p>1, a quantitative upper-incomplete-gamma formula for
   the conditioned maximum, with O(N^(-1/2)) logarithmic-CDF error on bounded
   centered windows. This supplies every fixed-order inverse-logarithmic
   correction in a single explicit coefficient formula.
2. A marked Poisson limit locating those extremes on the submacroscopic
   index scale N/(log N)^(1/p), jointly independent of the variance-clock
   Brownian bridge and the exponential conditioning slack.
3. The corresponding joint marked-Poisson/bridge/slack theorem for EVERY
   uniformly lacunary weight sequence, including the Fabius weights 2^(-j).
   This addresses the qualitative point-process and independence parts of
   Question 7 in the repository's lacunary-conditioning report. Sharp rates
   for the complete joint process remain open. (Editorial, 2026-09-30: that
   report, `../Sharp_Conditioning_Laws_Fabius_Lacunary_Series/`, now carries
   a reciprocal note at its Question 7.)

## Relationship to the repository

Inspected repository: VladimirReshetnikov/ProveIt.
Pinned commit: a4268e78ebd0f6bf71ba609c07f4b3415748f532.

The comparison explicitly distinguishes two earlier reports:
`Sharp_Conditioning_Laws_Fabius_Lacunary_Series` and
`Sharp_Conditioning_Laws_Uniform_Random_Series`, both under the Fabius
representation research directory. The latter already gives a general
variance-fraction theorem and polynomial variance clocks. Those are NOT
presented here as new. Exact pinned source links are in the bibliography.

These are manuscript proofs, not Lean/Rocq-certified or externally refereed
results. Worldwide historical priority has not been established. The article
does not depend on assuming the earlier manuscript theorems: it supplies the
local density estimates and conditional-likelihood arguments it uses.

## Rebuild the PDF

A standard TeX Live installation with newtx and the usual AMS packages suffices.

```sh
make pdf
```

Equivalently, run pdflatex twice on article.tex. `make clean` removes temporary
TeX files but retains article.pdf.

## Reproduce the numerical diagnostics

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

The delivered run used Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0,
SymPy 1.14.0, and mpmath 1.3.0. It passed six symbolic identities, generated
12 CDF comparison rows (p=2, N=32/128/512/2048, z=-1/0/1), and performed a
numerical stability rerun with a longer exact head, higher tail order,
and larger Fourier cutoff.

Output files (recorded in `data/`; a run writes them to `data-rerun/`
unless `--output` is given, and only `--output data` overwrites the recorded
files; as delivered, the default was `data/` itself, also for `--quick`):
- `data/maximum_table.csv`: all 12 parameter triples and diagnostic values.
- `data/verification.json`: symbolic results, versions, constants, and stability.

`--quick` omits N=2048 and the stability rerun. No internet connection,
GitHub credentials, repository checkout, or random seed is needed.

In this repository, on Windows, `uv run --no-project --with numpy==2.3.5
--with scipy==1.17.0 --with sympy==1.14.0 --with mpmath==1.3.0 python
code/verify.py` runs the diagnostics without a virtual environment; bare
`python` may not resolve, so use `py` or `uv`.

The numerical CDF evaluations are floating-point approximations. The
independent maximum formula is an exact FINITE PRODUCT mathematically;
its decimal evaluation is not exact arithmetic. Conditional CDFs use
numerical Fourier inversion and a Bernoulli--Hurwitz-zeta tail expansion.
Changing numerical settings is a stability check, not an interval-certified
error bound. There is no Monte Carlo simulation in this package.

## Further research

The final article section gives eight directions, including quantitative
joint-process rates, the first genuine finite-N conditioning correction,
regularly varying and nonuniform models, transition regimes, multiple
constraints, random weights, and certified computation/formalization.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batch 65 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`, every change to the program `ed. (2026-09-30)`.
The addressee line ("prepared for Vladimir Reshetnikov") and the
running head and title-page label "ProveIt research extension" are kept as
delivered, as for the other arrivals of the Fabius drafts tree; the package
is an archival arrival, not a ProveIt release.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-30)" is defined in the preamble (the theorem counter is
  unchanged). One note, after the numerical constants following
  Proposition `prop:constants`: the letter dictionary with
  `../Sharp_Conditioning_Laws_Uniform_Random_Series/`, which the article
  credits but whose constants it renames. There `M_p` (mean) is `A_p` here
  and `C_p` (variance) is `B_p` here, its `C_p = (1-1/p) M_p` is
  `B_p = (1-beta) A_p`, and its variance fraction `alpha_p(b)` is the index
  clock `F_p(b)`; the `C_p` here (the log-partition constant,
  `-Gamma(1-beta) zeta(1-beta)`) is a third constant. The mean function,
  total mean, normalizer and slack letters are also swapped. No label was
  renamed or removed.
- `article.pdf`: rebuilt from the amended source by the two `pdflatex`
  passes of the `Makefile` (MiKTeX pdfTeX 1.40.29): 21 pages as delivered,
  no error, undefined reference, multiply defined label, duplicate
  destination, or overfull box; every font is embedded and none is Type 3.
  The page carrying the note was rendered and inspected.
- `code/verify.py`: the default `--output` is `data-rerun/` instead of
  `data/`, so neither a plain run nor `--quick` overwrites the recorded
  files; the CSV writer passes `lineterminator='\n'` (the `csv` default is
  CRLF on every platform, which is why the delivered
  `data/maximum_table.csv` had CRLF line endings; it was normalized to LF on
  filing, batch 65) and the JSON writer `newline='\n'`. A rerun of the
  amended program on a copy (2026-09-30, the `uv` command above) wrote LF
  files with the recorded header and 12 rows; 50 of the table's cells differ
  from the recorded ones in the last digits (at most 3.6e-13 relative), and
  in `verification.json` only the stability entry `absolute_cdf_change`
  differs (6.1e-16 against 5.0e-16); both are floating-point noise of the
  platform, as the program's status line says.
- `README.md`: a pointer to the reciprocal note, the output location and the
  Windows command, and this section.
- Recorded, not changed: `requirements.txt` stays unpinned as delivered; the
  pinned command above is the one used for the rerun.
