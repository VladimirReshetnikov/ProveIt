# The Lacunarity Boundary

**Two-Moment Rigidity and Sharp Recovery of Geometric Uniform Spectra**

Research manuscript prepared for Vladimir Reshetnikov, 30 September 2026.

## Main result

For independent uniforms U_j on [-1,1], let X_a = sum_j a_j U_j.
Under a_(j+1) <= a_j/2 and sum_j a_j^2 = 1/3, the article proves

    sup_j |a_j - 2^(-j)|^2 <= (75/4) (19/675 - E[X_a^4]).

The fourth-moment deficit is nonnegative and vanishes only at the exact
dyadic spectrum. The resulting full-spectrum inverse modulus is exactly
Theta(sqrt(epsilon)) in total variation and Kolmogorov distance, including
in the predecessor's precisely defined infinitely smooth class.

Additional proved results include exact support rigidity, local prefix
conditioning Theta(2^r), testing sample complexity Theta(delta^(-4)), honest
reference-point confidence contraction of order N^(-1/4), and extensions to
geometric and nongeometric relative-ratio reference cones.

This answers the question titled "The sharp separation boundary rho=1/2"
in the repository article identified in SOURCES.md. The supercritical
comparison is a result attributed to that predecessor; the critical proofs
are independent of its unformalized quantitative theorems.

## Contents

- `article.pdf`: compiled research article.
- `article.tex`: complete self-contained LaTeX source, including bibliography.
- `code/verify.py`: standard-library exact rational regression checks.
- `results/verification.json` and `.txt`: recorded run with 29,776 assertions.
- `results/witness_diagnostics.csv`: 65-digit Decimal evaluations of explicit formulas.
- `results/build_report.txt`: compilation and PDF validation summary.
- `PROOF_AUDIT.md`: theorem dependencies and limitations.
- `SOURCES.md`: pinned repository provenance and primary literature.
- `Makefile`: optional build and verification commands.

## Reproduce

Compile with a TeX distribution containing the packages listed at the top
of `article.tex`:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

Alternatively, run `pdflatex article.tex` repeatedly until references stabilize.
No shell escape, downloaded assets, or network access is required.

Run the computational checks with Python 3.10 or later:

    python code/verify.py

The program uses only the standard library and writes by default to
`results-rerun/`, preserving the recorded output. To select another output
location:

    python code/verify.py --output-dir /path/to/output

## Verification status

The universal claims are supported by the conventional mathematical proofs
in the article. The code checks finite instances and algebraic identities;
it is not a replacement for those proofs and is not formal verification.
The analytic Hellinger estimates are not certified by numerical integration.
Decimal outputs are diagnostics, not outward-rounded interval enclosures.

No Lean build was run. The manuscript has not been independently peer
reviewed. The contribution is presented relative to an explicitly documented
repository question; exhaustive literature priority has not been established.
No ProveIt repository files were changed.
