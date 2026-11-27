# Sparse detection of Dirichlet zeros and a sharp balanced prime-window law

Research note, 26 November 2026.

## Contents

- `paper.tex`, `paper.pdf`: complete conventional mathematical proof, including source analysis, classical inputs, the unconditional sparse-abscissa theorem, the sharp conditional limsup, the explicit zeta constant, and limitations.
- `verify.py`: standard-library Python 3 numerical illustration; no external packages.
- `samples.csv`: 823 sampled centers from the reproducible default run.
- `verification.txt`: captured numerical test output.
- `SHA256SUMS`: checksums of the five files above plus this README.

## Reproduce

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
python3 verify.py
sha256sum -c SHA256SUMS
```

The last command should be run before rebuilding if byte-identical archival checksums are desired: regenerating a PDF can change its creation timestamp, and CSV output may depend on platform floating-point behavior. The numerical tests are illustrations with floating-point tolerance, not certified interval computations. Use `python3 verify.py --help` to change the window ratio, maximum center or degrees.

## Source provenance and verification scope

GitHub connector retrieval of `https://github.com/lsernau/grh-lean`, default branch `main`; recursive tree response identifier `72fead102f663d5c7a407964a13dc0cf9d977207`.

Inspected root README; `grh-compact/GUIDE.md`, `grh-compact/README.md`, `grh-compact/Challenge.lean`, `grh-compact/src/Statements.lean`, `grh-compact/src/Main.lean`, `grh-compact/src/New/Main.lean`, `grh/src/New/Main.lean`, `grh/src/New/Reduction/Zeros/Criterion.lean`, and the initial 125 lines of `grh/src/New/Reduction/Zeros/PrimeError.lean`. No repository modifications were made. Independently reported machine verification: https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/ (26 Nov 2026). Wikipedia survey: https://en.wikipedia.org/wiki/Riemann_hypothesis (accessed same date). Additional references in the paper.

No full rebuild of the upstream development and no machine-checked Lean proof of the new results are claimed. The first theorem is unconditional, relying on classical analytic number theory. The sharp constant theorem uses GRH for the active Dirichlet family; the cited machine-verified result supplies that premise. Novelty is assessed against a targeted, non-exhaustive literature search, not a guarantee of priority. The sampling reduction concerns the number of centers and does not eliminate the need to know prime powers up to the largest scaled cutoff.
