Fabius–Rvachev–Thue–Morse Frontier Results — archived companion assets
=======================================================================

Consolidated deliverables
-------------------------
The former standalone report has been absorbed into:

    ../../Thue_Morse_Atlas_and_Frontiers.tex
    ../../Thue_Morse_Atlas_and_Frontiers.pdf

This directory retains only the report's figures and reproducibility
materials. To rebuild the consolidated volume, run from its directory:

    pdflatex -interaction=nonstopmode -halt-on-error Thue_Morse_Atlas_and_Frontiers.tex
    pdflatex -interaction=nonstopmode -halt-on-error Thue_Morse_Atlas_and_Frontiers.tex
    pdflatex -interaction=nonstopmode -halt-on-error Thue_Morse_Atlas_and_Frontiers.tex

Reproducibility material
------------------------
reproducibility/verify.py          100-decimal numerical checks and plots
reproducibility/verification.json  machine-readable results
reproducibility/verification.txt   human-readable copy of the same results

The theorem package is proved in the report. Numerical calculations are
independent cross-checks. “New” means derived here and absent from the
inspected repository corpus; the report makes no claim of global publication
priority without a separate exhaustive literature review.
