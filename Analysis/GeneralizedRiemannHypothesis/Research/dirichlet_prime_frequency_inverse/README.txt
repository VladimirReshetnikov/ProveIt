Hearing a differential operator and a conductor at one prime
November 2026

Read prime_frequency.pdf for the full proof. prime_frequency.tex is the
self-contained LaTeX source. Build with two runs of pdflatex or latexmk -pdf.

Theorems 1 and 2 give the prime-frequency formula and finite reconstruction.
Corollary 4 distinguishes the zero multisets of different operators in
short intervals. Theorem 5 gives a version using full complex zeros whose
proof is independent of Dirichlet GRH.

To reproduce the symbolic example and sharpness checks:
    python check_algebra.py
Requires SymPy. Compare with algebra_output.txt.

To reproduce the floating-point example for zeta and its completed derivative:
    python zero_example.py
Requires NumPy, SciPy, and mpmath. Compare with zero_example_output.txt.
The script computes its own ordinates. It does not download a table.
Floating-point output can vary in the last displayed digit by platform.

The proofs are mathematical arguments in the paper. The scripts check
examples. Source versions and attributions are in the paper's final section.
