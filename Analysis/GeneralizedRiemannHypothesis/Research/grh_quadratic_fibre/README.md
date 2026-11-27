# The quadratic-fibre transition for squarefree products of small primes

Research note for ProveIt, 27 November 2026.

## Contents

- `quadratic_fibre.tex` — self-contained mathematical manuscript, including references.
- `quadratic_fibre.pdf` — compiled 10-page manuscript.
- `SOURCE_AUDIT.md` — precise source provenance and scope of inspection.
- `verify.py` — standard-library Python checks of parity identities and exact prime-product counts.
- `verification.txt` — recorded successful run of the script.
- `critical_window.csv` — numerical illustrations of the sharp finite-sampling correction, computed from exact rational coefficients.
- `prime_counts.csv` — exact integer dynamic-programming counts for modulus 101.
- `SHA256SUMS` — hashes of the foregoing files.

## Reproduction

Run `pdflatex -interaction=nonstopmode -halt-on-error quadratic_fibre.tex` twice (standard TeX Live packages). Run `python3 verify.py` to regenerate the CSV files and repeat the finite checks. Run `sha256sum -c SHA256SUMS` before regenerating any files if you wish to verify the distributed bytes.

## Status

The proof uses the exported Dirichlet GRH theorem at the indicated upstream revision. The new probabilistic lemma is unconditional. The manuscript is a mathematical proof, not a new Lean development; the upstream build was not independently rerun here. Exact computations are illustrative checks, not a substitute for proof. The new contribution is the uniform crossover and first-order correction, not the exact quadratic Fourier coefficient or the earlier bounded quotient result. Global publication priority has not been certified. No repository files were changed.
