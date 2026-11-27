Dirichlet characters from a single Li heat kernel
Research note dated 27 November 2026

Read li_heat_kernel.pdf for the statements, proofs, source comparisons,
and numerical certificate derivation. li_heat_kernel.tex is the complete
editable manuscript. It has an embedded bibliography and no external
figures or source includes.

Build the paper with a standard TeX Live installation:
    pdflatex -interaction=nonstopmode -halt-on-error li_heat_kernel.tex
    pdflatex -interaction=nonstopmode -halt-on-error li_heat_kernel.tex

Reproduce the conductor-five check with Python 3.10+ and mpmath 1.3.0,
using the default interpreter mode with assertions enabled:
    python3 checks/quartic_echo.py
    python3 checks/quartic_rectangle.py

The first program encloses a simple zero in two nested disks and excludes
other critical-line zeros in the height range. The second counts all
zeros in a rectangle containing the entire closed critical-strip segment.
It imports arithmetic routines from quartic_echo.py. The outputs of the
two programs are in checks/expected.txt and checks/rectangle_expected.txt.

Mathematical scope
The general results use Dirichlet GRH, classical Li coefficient
asymptotics, and the one-sided Dirichlet zero counts. The results concern
fixed primitive characters, with repetitions allowed in products of zero
factors. The paper distinguishes relative agreement of infinite Fourier
tails from eventual recovery with finitely many noisy Li coefficients.
The numerical certificate is a separate finite result. The new paper is
a written mathematical proof. The bibliography links to the independent
machine-check records for the upstream Lean theorem.

Source revisions
lsernau/grh-lean
    72fead102f663d5c7a407964a13dc0cf9d977207
VladimirReshetnikov/ProveIt
    1a50d416ba30b91595db12d7437f0328a32b0468
