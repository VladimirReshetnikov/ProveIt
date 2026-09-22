# Untransformed Leray Cycles for Radius-Free Hahn Analytic Residues

Research article, September 21, 2026. The PDF has 24 pages, including the
cover, contents, and bibliography.

## Main result

For a convergent complex map germ f with an isolated zero, and a positive-support
Hahn perturbation F=f+E, the article constructs a single finite-cover,
coefficientwise Hahn cycle representing the residue of the original form
H dz/(F_1 ... F_n). No common convergence radius for the coefficient germs of
E or H is assumed. The protecting cycle depends only on f and a positive
valuation lower bound for E, not on the individual perturbation or numerator.

A second construction gives an exact equation-adapted cycle, with a
support-controlled pole-free homotopy to the protecting cycle. The article
also gives a separate formal-coefficient extension, degree normalization,
a regular-fiber trace formula, and a mixed six-sheeted worked example.

This addresses the original-integrand cycle problem stated in the Surreal
repository's contours-and-stokes report. The chain category and all hypotheses
are explicit. The claim is not that a named published conjecture has been
settled, nor that historical priority has been certified.

## Files

- article.tex: standalone LaTeX source with internal bibliography.
- article.pdf: typeset article.
- code/checks.py: executable exact symbolic checks for the examples.
- data/checks.json: recorded results; 632 checks passed with SymPy 1.14.0.
- SEARCH_NOTES.md: repository provenance and targeted literature-search notes.
- build.sh: rebuild the PDF and run the checks.

## Rebuild

A standard TeX Live installation with latexmk and the packages named in the
preamble suffices. No external bibliography file, graphics, shell escape, or
font files are required.

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

For the exact checks, install Python 3.10 or later and SymPy, then run:

    python code/checks.py --output data/checks.json

The included build.sh performs both commands. All calculations in checks.py
are exact. The general arbitrary-support arguments are human-readable proofs,
not proof-assistant formalizations. The finite tests do not establish those
general theorems and do not establish novelty.

## Validation of this delivery

The final LaTeX build has no undefined references, LaTeX errors, overfull
boxes, or underfull boxes. The PDF was rendered for visual inspection.
All 632 exact symbolic checks passed. No fonts or generated TeX intermediates
are included in the archive.
