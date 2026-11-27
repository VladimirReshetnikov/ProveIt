# Zeros and poles of translated Dirichlet L-functions

Open **local_divisors.pdf** for the eleven-page paper. The editable sources are
**local_divisors.tex** and **translations.tex**. Keep them in the same directory.

## Results

- Theorem 1 gives a single triple-logarithmic height window that contains a zero and a pole of the order-r multiplicative finite difference of a primitive Dirichlet L-function. Both survive cancellation for every nonzero real step in a prescribed bounded range, simultaneously.
- Theorem 9 gives a shrinking window of radius C/log log T when the translation step is below any fixed fraction of the local mean spacing. Its constant is explicit up to an arbitrarily small additive margin. Corollary 10 handles bounded normalized steps separated from the positive integers.
- Theorem 8 treats compact families of translated characters, with uniform signed excess and lower bounds for the cost of matching zero lists subject to an allowed translation.
- The supporting results on unshifted multiplicity vectors are compared in Section 2 with earlier ProveIt papers, including previous triple-logarithmic bounds. Section 9 gives an exact finite prime example and further questions.

The paper uses the published Dirichlet GRH theorem and the classical explicit
formula and argument estimates. It treats arbitrary multiplicities.
The new results have written proofs. They have not been formalized in Lean.
The upstream proof was inspected and its independent verification record was
consulted. No local upstream build was performed for this paper.
The references record the source comparison. Historical priority is provisional.

## Build

With a standard full TeX Live installation, run these commands in this directory.

    pdflatex -halt-on-error local_divisors.tex
    pdflatex -halt-on-error local_divisors.tex

## Reproduce the checks

    python3 checks/lattice_check.py
    python3 checks/directional_star.py
    python3 checks/translation_check.py --zero-table
    python3 checks/prime_window_demo.py
    python3 checks/prime_window_demo.py --paper-kernel

The first three scripts use only the Python standard library. The lattice checker verifies the divided-difference and bin identities with rational arithmetic on small test grids. The modulus-eight
certificate proves an inequality for the actual prime weights by rational
lower bounds. The translation certificate bounds the two-prime coefficient
through step zero by exact arithmetic. Its optional zero-table exercise uses
the numerical table under the accuracy and completeness assumptions stated
in the output. The prime-window demonstration uses NumPy and SciPy.
Its two modes check the normalization of the explicit formula against a finite
table of zeta ordinates and a truncated prime-power sum. Recorded results and
quadrature settings are in the checks directory. To regenerate the ordinate
table, use the option described in checks/window_demo.txt with mpmath installed.

The numerical comparisons are diagnostics. The two asymptotic window bounds
and their uniformity are proved in the paper.
