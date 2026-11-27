# Sharp error correction for sparse Dirichlet spectra from small primes

Research packet, 2026-11-27. Suggested location if incorporated into ProveIt:
`Analysis/GeneralizedRiemannHypothesis/Research/prime_sparse_recovery/`.
No repository files were changed.

## Contents
- `prime_sparse_recovery.tex` and `prime_sparse_recovery.pdf`: research manuscript, including full human-readable proofs, source analysis, and references.
- `check_examples.py`: exact finite bias, corruption, and indistinguishability certificates for q=24; numerical linear-programming checks; exact finite-bias extremizer.
- `example_output.txt`: captured execution output.
- `prime_pools.csv`: all 464 primes, residues, exact integer weights, and the 202-prime subset membership.
- `LEAN_PLAN.md`: formalization dependency plan, explicitly not a checked Lean proof.
- `SOURCE_NOTES.md`: inspected repository paths and provenance.
- `THINNING_ALGORITHM.md`: deterministic construction recipe and exact certificate interface.
- `SHA256SUMS`: integrity manifest.

## Reproduce
```
pdflatex -interaction=nonstopmode -halt-on-error prime_sparse_recovery.tex
pdflatex -interaction=nonstopmode -halt-on-error prime_sparse_recovery.tex
python check_examples.py
sha256sum -c SHA256SUMS  # run before rebuilding if verifying original bytes
```
The script uses Python 3 (3.10+ recommended), NumPy and SciPy for the numerical LP. Its bias, margin, and ambiguity tests use exact integer/rational arithmetic. The LP checks are illustrative, not formal verification. The theorem uses classical Dirichlet GRH as exported by the pinned upstream Lean development, not general automorphic GRH. The finite-group theorems and computational checks are independent of GRH. The new proofs are not kernel checked; absolute constants in the asymptotic prime bound are not evaluated. Originality is provisional rather than an exhaustive priority claim.
