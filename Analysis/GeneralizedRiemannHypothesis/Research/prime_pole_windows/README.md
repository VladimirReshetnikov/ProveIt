# Reading arithmetic weights from poles of a prime series

The eight-page paper is in prime_pole_windows.pdf. The file prime_pole_windows.tex is its complete standalone LaTeX source.

Theorem 1 determines exactly what can be recovered from the residues on a short segment of a vertical line. Theorem 2 proves local independence of zero multiplicities in the whole critical strip, independently of GRH. Corollary 3 identifies a natural boundary. Theorem 4 classifies which sets of lines can carry poles. Corollary 5 compares the multiplicities of two primitive Dirichlet functions in both directions.

## Reproducing the files

Run these commands in the extracted folder using a standard TeX Live installation with Latin Modern, the AMS packages, microtype, fancyhdr, xcolor, geometry, booktabs and hyperref.

    pdflatex -halt-on-error prime_pole_windows.tex
    pdflatex -halt-on-error prime_pole_windows.tex

The finite arithmetic checks require Python 3.8 or later and the standard library.

    python3 code/verify_layers.py

They compare enumerated power images with the prime-power decomposition of unit groups, verify Möbius cancellation in Euler coefficients, and enumerate all 20 possible patterns modulo 31. Recorded output is in code/verification.txt. These checks cover the discrete computations. The analytic estimates are proved in the paper.

The optional numerical illustration requires Python 3 and mpmath 1.3.0.

    python3 code/window_demo.py

The script computes one zeta zero and one Dirichlet beta zero in the same small window, checks the other function at each ordinate, and exhibits the two recovery equations modulo four. Recorded output is in code/window_demo.txt. The calculation uses ordinary high-precision arithmetic.

## Source revisions

The paper uses the public Dirichlet GRH endpoint in lsernau/grh-lean at 72fead102f663d5c7a407964a13dc0cf9d977207. The comparison with VladimirReshetnikov/ProveIt uses 61e72d75affa1084cf3ac4f66d199f54efde05fe. Permanent source links and the mathematical references are in the paper. The new proof is written in LaTeX and has not been formalized in Lean.
