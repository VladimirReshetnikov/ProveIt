From Finite Blacklists to Freiling Symmetry
===========================================

Contents
--------
From_Finite_Blacklists_to_Freiling_Symmetry.tex
    Complete LaTeX source for the research article.

From_Finite_Blacklists_to_Freiling_Symmetry.pdf
    Compiled 19-page article (US Letter).

verification.py
    Independent exhaustive checks for all one-blacklist systems through n=7,
    plus the two critical labelled-enumeration examples reported in the paper.

verification_output.txt
    Captured output from a successful verification run.

SHA256SUMS.txt
    SHA-256 checksums for the principal files.

Build
-----
A current TeX Live installation with the packages named in the source is
sufficient. For example:

    pdflatex From_Finite_Blacklists_to_Freiling_Symmetry.tex
    pdflatex From_Finite_Blacklists_to_Freiling_Symmetry.tex

Verification
------------

    python3 verification.py

The exhaustive n=7 check is the largest step and may take several seconds to a
few minutes, depending on the machine.

Status
------
AI-assisted and unrefereed. Classical results are credited in the article;
no historical-priority claim is made for the finite refinements without a
more exhaustive literature review.
