Recovering individual zeta zeros from Li coefficients
Research note • 26 November 2026

li_ritz.pdf is the complete seven-page paper. li_ritz.tex is its self-contained
LaTeX source. To rebuild in a standard TeX Live installation run
    latexmk -pdf li_ritz.tex

Theorem 1 proves the two-term logarithmic Ritz error law. Theorem 3 gives the
finite simplicity and enclosure test. Corollary 4 gives a Hankel determinant
asymptotic. Corollary 5 treats primitive Dirichlet functions around an arbitrary
fixed height. The asymptotic arguments use the zero-location theorems as
inputs and are proved in the paper. The Python verification applies to the
four tabulated enclosures.

To reproduce the certified calculation from analytic Taylor data, run
    cd verification
    python3 certify_moments.py
    python3 verify_zeros.py

These two commands use only the Python standard library. The first regenerates
certified_moments.json from bounded Euler–Maclaurin and Taylor expansions.
The second checks witness.json with exact rational arithmetic and prints the
enclosures in verified_zeros.txt. CERTIFICATE.md explains the witness format
and the mathematical checks. The proof of these bounds uses RH to identify
Taylor-derived moments with the positive zero measure.

Optional floating-point illustration, from verification/
    python3 ritz_demo.py

This script requires mpmath 1.3.0. It generates the convergence table and
compares with independent zeta-zero evaluations. Its output is recorded in
ritz_output.txt. All computations can run offline once the corresponding
software is installed.
