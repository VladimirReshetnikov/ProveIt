FLATTENING A SPHERE ALMOST EVERYWHERE
Verification and explanation, 23 November 2026

Main files
  globe_flattening_verification.pdf  Complete mathematical report.
  globe_flattening_verification.tex  Editable LaTeX source of the report.
  original_claim.md                 The supplied document, unchanged.
  figures/*.pdf                    Vector explanatory figures.
  figures/make_figures.py           Reproducible figure-generation source.

Verdict
The main existence theorem is correct after a minor parameter-range repair.
The report verifies all five refinement estimates and classical differentiability,
proves the geometric and area assertions, and explains the unavoidable failure
of local Lipschitz regularity. It gives stronger statements about the positive
exceptional area in every open subset, and carefully separates a nearby
exact-area result with approximate derivatives from the unresolved-by-this-report
question with classical derivatives. No novelty certification or proof-assistant
formalization is claimed.

Build
From this directory, run:
  latexmk -pdf -interaction=nonstopmode -halt-on-error globe_flattening_verification.tex
Alternatively, run pdflatex on the source twice (or until references settle).
The included vector figures suffice; Python is not required to compile.

To recreate the figures, run:
  python figures/make_figures.py
The script uses NumPy and Matplotlib.

The figures are explanatory models, not sampled realizations of the limiting
spherical homeomorphism. The proof is analytic and does not depend on numerical
experiments. Bibliographic URLs appear in the report.
