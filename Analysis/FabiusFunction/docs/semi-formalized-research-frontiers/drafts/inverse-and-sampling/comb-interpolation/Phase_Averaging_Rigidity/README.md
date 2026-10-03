# Rigidity and Quantitative Limits of Phase Averaging
## in Fabius–Rvachev Quadrature

Research article prepared for Vladimir Reshetnikov, September 28, 2026.

## Contents

- `article.pdf`: the compiled 21-page article (20 pages as delivered; the
  editorial note of 2026-09-30 adds one).
- `article.tex`: complete, self-contained LaTeX source, with its bibliography.
- `verify.py`: exact rational checks and optional high-precision diagnostics.
- `verification.json`: machine-readable results of the supplied default run.
- `verification_output.txt`: human-readable transcript of that run.
- `SOURCE_AUDIT.md`: repository provenance, inherited results, and novelty boundaries.
- `Makefile`: PDF rebuild and verification commands.

## Results

For a rational mesh M=a/b in lowest terms and target polynomial degree r,
uniform exactness under every overall translation is equivalent to invariance
of the signed phase measure under rotation by 1/L, where

    L = b * 2^max(0, r - v2(a)).

A finite exact filter needs at least L distinct phases. At the minimum it is
necessarily the equally weighted regular L-gon, even when negative weights
are permitted. For irrational M, Haar measure is the only phase measure
uniformly exact even on constants. An annihilating-polynomial argument gives
explicit positive uniform moment-error bounds below the rational support
threshold, and for every finite support size in the irrational case.

The Fourier analysis also supplies an inverse-square odd-dilation comparison,
a stronger log-Gaussian relative bound uniform in the odd mesh factor, and
explicit first-defect phase and simple-zero estimates.

## Status and scope

The article contains complete ordinary mathematical proofs. The new results
have not been independently peer reviewed or checked in Lean. No repository
build was performed. The repository already contains phase-classification
results; these are credited in the article, not claimed as newly solved.
The candidate contributions are the signed-filter classification and its
quantitative cost consequences, and the stronger uniform bounds. A targeted
literature check does not certify worldwide novelty.

The phase-count lower bound is for a single fixed filter that works for every
overall lattice translation. It is not a lower bound for arbitrary Gaussian
quadrature, a rule at one fixed phase, or phase-dependent weights. Higher
maximality at the special phases is not claimed.

## Rebuild the PDF

A standard TeX Live installation containing the packages named at the beginning
of `article.tex` is sufficient. No external graphics or local font files are
required. Run:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

Alternatively run `make pdf`. The PDF was generated with pdfTeX and visually
inspected after rendering. The final build has no undefined references or
overfull boxes; bibliography URL wrapping produces harmless underfull boxes.

## Reproduce the verification

Python 3.10 or newer is recommended. Exact checks require only the standard
library:

    python verify.py --skip-numerical --output exact_results.json

The full run additionally uses `mpmath`:

    python -m pip install mpmath
    python verify.py --output verification.json

The recorded run used 75 decimal digits for its optional numerical checks.
It passed 261 exact quadrature/moment/reindexing assertions and 53,760 exact
frequency-arithmetic assertions, plus 240 inverse-square comparisons, 240
multiscale-envelope comparisons, 36 derivative checks, and 12 Fourier
normalization checks. The numerical counts describe tested instances, not
independent mathematical proofs or certified interval calculations. The
largest Fourier comparison error was approximately 6.40e-19 using 200
positive odd harmonics, with an acceptance tolerance of 1e-18.

`--max-level` controls the exact dyadic test range (default 4, allowed 0–7).
The exact evaluator is deliberately transparent rather than optimized; higher
levels can be considerably slower. No network connection is used by the script.

## Repository baseline

VladimirReshetnikov/ProveIt, commit
`37e61c1fdec28c6e7ab7ff445043993077b42cbd`.
See `SOURCE_AUDIT.md` and the article bibliography for the inspected paths.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batch 64 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-30)" is defined in the preamble. One note, after Research question
  "Arithmetic behavior near rational scales" and its discussion, records that
  for fixed `K` the question is answered by Theorem `thm:resonance` of the
  later unreviewed draft `../Approximate_Phase_Rigidity/`, for the optimal
  error itself: near a reduced rational `a/b` the least error over mass-one
  filters with at most `K` atoms (positive, real signed or complex, nodes and
  weights depending on `M`) has exact order
  `|M-a/b|^max(0, v2(a)+1+floor(log2(K/b))-r)` for `K >= b` and stays
  bounded away from zero for `K < b`, attained by a regular polygon; the
  constants, their uniformity as `K` grows and the optimal leading constants
  remain open there, and the under-budget infimum of the preceding question
  at the rational mesh itself is not computed. The title page no longer sets
  a PDF page anchor (it duplicated the destination `page.1`).
- `article.pdf`: rebuilt from the amended source by the three passes above
  (MiKTeX pdfTeX 1.40.29): 21 pages (20 as delivered), no error, undefined
  reference, duplicate destination or overfull box, every font embedded and
  none of Type 3; the three underfull boxes are the bibliography URL entry
  noted above. The page carrying the note was rendered and inspected.
  `verification.json` and `verification_output.txt` are unchanged.
- `README.md`: the page count under "Contents", and this section.
