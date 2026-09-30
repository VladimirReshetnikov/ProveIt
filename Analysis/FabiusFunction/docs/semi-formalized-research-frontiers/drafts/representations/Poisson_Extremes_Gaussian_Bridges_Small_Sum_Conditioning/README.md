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
   for the complete joint process remain open.

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

Output files:
- `data/maximum_table.csv`: all 12 parameter triples and diagnostic values.
- `data/verification.json`: symbolic results, versions, constants, and stability.

`--quick` omits N=2048 and the stability rerun. No internet connection,
GitHub credentials, repository checkout, or random seed is needed.

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
