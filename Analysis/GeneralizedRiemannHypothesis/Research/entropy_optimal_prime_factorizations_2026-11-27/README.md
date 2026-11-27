# Entropy-optimal simultaneous factorizations into distinct small primes

Research packet for ProveIt, 27 November 2026.

## Result

For fixed factor count and positive quota proportions, define the entropy threshold as the maximum, over all groupings of factor labels, of the logarithm of the number of compatible grouped residue tuples divided by the entropy of the grouped proportions. The paper proves an unconditional matching counting lower bound and, from Dirichlet GRH, an upper bound with additive error O(log M / log B) using distinct primes in [B log²(2M), 2B log²(2M)], where M is the lcm of the moduli. For arbitrarily slowly diverging B (at most a fixed power of log M), the threshold is asymptotically exact. A uniform version permits all entropy-feasible interior quota profiles for the same modulus tuple to use one common pool.

## Files

- `entropy_factorizations.tex` — self-contained LaTeX paper, complete proof and bibliography.
- `entropy_factorizations.pdf` — compiled paper (11 pages).
- `source_audit.md` — repository analysis, exact consulted blob IDs, references and limitations.
- `experiment.py` — standard-library Python exact finite support computation, counting obstruction and pair-repair inclusion checks.
- `experiment_results.json` — reproducible output with explicit prime lists and support counts.
- `experiment.log` — recorded stdout of the test run (identical JSON data).
- `SHA256SUMS` — integrity manifest.

## Reproduce

```
pdflatex -interaction=nonstopmode -halt-on-error entropy_factorizations.tex
pdflatex -interaction=nonstopmode -halt-on-error entropy_factorizations.tex
python3 experiment.py
sha256sum -c SHA256SUMS  # run before regenerating the PDF (timestamp may differ)
```

No experiments are assumptions of the proof. The result is a conventional mathematical argument using the repository's Dirichlet GRH as input, not a Lean-checked theorem. The finite-group and lower-bound proofs are unconditional. The theorem gives support, not near-uniform counts, deletion robustness, or one pool for all moduli. Literature comparison and source audit are targeted; priority is not certified. No source repository modifications were made.
