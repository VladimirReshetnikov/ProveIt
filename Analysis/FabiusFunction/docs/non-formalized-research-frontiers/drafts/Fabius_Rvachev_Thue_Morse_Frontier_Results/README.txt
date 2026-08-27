Fabius–Rvachev–Thue–Morse Frontier Results
============================================

Main deliverables
-----------------
Fabius_Rvachev_Thue_Morse_Frontier_Results.tex
Fabius_Rvachev_Thue_Morse_Frontier_Results.pdf

The figures/ directory is required when recompiling the LaTeX source.
Compile from this directory with:

    latexmk -pdf -interaction=nonstopmode -halt-on-error \
      Fabius_Rvachev_Thue_Morse_Frontier_Results.tex

Reproducibility material
------------------------
reproducibility/verify.py          100-decimal numerical checks and plots
reproducibility/verification.json  machine-readable results
reproducibility/verification.txt   human-readable copy of the same results

The theorem package is proved in the report. Numerical calculations are
independent cross-checks. “New” means derived here and absent from the
inspected repository corpus; the report makes no claim of global publication
priority without a separate exhaustive literature review.
