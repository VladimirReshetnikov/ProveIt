# Reconstructing complete multipartite graphs from Ehrhart polynomials

The paper is multipartite-ehrhart.pdf. To build it from the editable sources, run the following command in this directory with a standard TeX Live installation.

    latexmk -pdf multipartite-ehrhart.tex

The input files combinatorics.tex, inverse.tex, interlacing.tex, zeros.tex and numerator-threshold.tex contain the proofs. The main file contains the references. Keep roots.pdf beside the sources when rebuilding.

## Exact verification

Run the following commands with ordinary Python, with assertions enabled.

    python verify.py
    python split_interlacing.py
    python matching_threshold.py
    python numerator_check.py

* verify.py checks lattice counts by independent edge-step enumeration, exact cross-degrees, inverse reconstruction, the matching-deletion identity, and the four off-line roots in Davis's example. Its expected output is checks.txt.
* split_interlacing.py certifies all positive n for each of the 20 singleton-insertion steps. It uses SymPy (tested with 1.14.0). Its expected output is interlacing_checks.txt. The proof of the polynomial degree bounds that make the finite certificate conclusive is in the paper.
* matching_threshold.py verifies the first dimension with a nonreal numerator root in the matching-deletion family. Proposed endpoints are rounded to rationals and checked by exact integer arithmetic. Its expected output is matching_threshold_checks.txt.
* numerator_check.py distinguishes the two numerators in dimension 169 by exact Sturm root counts. Its expected output is numerator_checks.txt.

The first, third and fourth programs use only the Python standard library. The general reconstruction theorem, limiting-strip theorem, and two asymptotic threshold results have mathematical proofs in the manuscript.

## Numerical figure

root_positions.csv contains the plotted roots. Running the following command regenerates it and roots.pdf using NumPy, mpmath and Matplotlib.

    python root_figure.py

The illustrated points are numerically located and refined using the polynomial recurrences. The arguments proving the limiting zero counts and the exact finite thresholds are independent of the figure.

## Source snapshot

The ProveIt input is the Analysis/GeneralizedRiemannHypothesis tree of VladimirReshetnikov/ProveIt at commit 641cd6296144d7c29bcc6569655b473647428b1b. The relevant graph argument is in Article/sections/gra.tex. The main manuscript links to the pinned file and the primary mathematical sources. The new results are unconditional and have not been formalized in Lean.
