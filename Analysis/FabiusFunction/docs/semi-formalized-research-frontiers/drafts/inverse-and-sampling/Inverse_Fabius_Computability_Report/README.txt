COMPUTABILITY OF THE INVERSE FABIUS FUNCTION
=============================================

Contents
--------
inverse_fabius_computability.tex
    Complete LaTeX source of the report.

inverse_fabius_computability.pdf
    Rendered 29-page report.

inverse_fabius_computability_experiments.py
    Exact-rational Python supplement.  It uses only the Python standard
    library and documents the finite Thue--Morse spline, endpoint-mass bounds,
    interval-mass check, and a certified comparison/bisection demonstration.

numerical_output.txt
    Captured output from the Python supplement with its default arguments.

SHA256SUMS.txt
    SHA-256 digests of the preceding files and this README.

Repository snapshot
-------------------
The documentation audit and all repository-relative novelty statements are
pinned to ProveIt commit:

    40fdea4cc0a728189f357389e3f114a2cb00e561

Build and validation
--------------------
The PDF was built with pdfLaTeX/latexmk.  The final log has no unresolved
references, overfull boxes, or underfull-box warnings.  The PDF was checked
with pdfinfo, pdftotext, PyMuPDF preflight, and a full 29-page Poppler render.

Reproduce the numerical supplement
----------------------------------
Run:

    python inverse_fabius_computability_experiments.py

No numerical experiment is used as a premise of the computability proof.
