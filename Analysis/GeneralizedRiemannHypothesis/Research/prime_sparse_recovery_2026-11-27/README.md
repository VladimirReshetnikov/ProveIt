# Error-correcting prime samples for sparse Dirichlet character mixtures

Research packet, 27 November 2026.

**Main result.** Assuming the Dirichlet GRH theorem exported by the supplied Lean development, a universal set of O_epsilon(k² log Q) distinct primes of size O_epsilon(k² log² Q) suffices to recover any k-sparse complex mixture of primitive Dirichlet characters of conductor ≤ Q. The convex decoder tolerates e known erasures and t unknown corruptions if e+2t < (1-epsilon)m/(2k). The threshold is sharp up to arbitrarily small relative loss and integer rounding when Q contains a prime modulus congruent to 1 modulo 4k. GRH guarantees such a modulus for Q sufficiently large compared to k² log²(2k).

## Files

- `prime_sparse_recovery.tex`, `prime_sparse_recovery.pdf`: full mathematical proof, including a stability estimate, unconditional decoding and obstruction theorems, source analysis, and arithmetic application.
- `source_audit.md`: exact GitHub paths, inspected blob IDs, relationship to the existing Article and verification status.
- `formalization.md`: precise dependency and mathematical interface plan for Lean; not compiled Lean code.
- `check.py`: reproducible example; full complex dictionary of 197 primitive characters for Q=31, real-subdictionary LP recovery, and a complex cyclic packet collision. `check_output.txt` records the actual run.
- `sample_primes.txt`: the 1,616 distinct primes in that example.
- `certify_gram.py`, `certificate_output.txt`: independent exact rational/integer check of Gram deviation ≤ 61/1000 for the full complex dictionary on this prime set. Taylor and Machin bounds account for all rounding. This certifies a positive decoder margin for the example, not the uniform theorem.

## Reproduce

From this directory, run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error prime_sparse_recovery.tex
pdflatex -interaction=nonstopmode -halt-on-error prime_sparse_recovery.tex
python -m pip install numpy scipy sympy
OPENBLAS_NUM_THREADS=1 python check.py
OPENBLAS_NUM_THREADS=1 python certify_gram.py
```

The experiment regenerates the sample list with a fixed random seed; minor solver output differences are possible. The certificate can also run independently on the supplied list. The numerical LP handles the real-character subdictionary only; the full complex convex theorem is proved on paper. No changes to the supplied repository were made. Novelty is proposed relative to the inspected sources; no comprehensive priority claim or independent formal verification is made.
