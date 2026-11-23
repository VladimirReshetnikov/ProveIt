# Verification record

The four exact computation suites passed. Their complete stdout is retained
in the corresponding `.log` files; `status.json` records commands, exit codes,
Python version, and the SHA-256 hashes of the executed checker sources.

- Integer polynomial normalization: 41 scalar components of 37 named
  relations, checked by exact coefficient equality without sampling.
- Circle algebra: 17 symbolic identity groups, checked using SymPy.
- Five solid realizations: exact arithmetic in Q(sqrt(5)), including all
  supporting triples, supporting faces, edges, regularity, and incidence.
- Measurement observations: 6 symbolic groups, 13 levels with outward rational
  interval arithmetic, and 512 finite-sum/refinement checks.

`source_audit.json` records source inspection, Python syntax parsing, and two
checks that the Lean build helper rejects output paths overlapping its
upstream checkout. These checks do not run Lean.

`pdf_quality.json` records the PDF build, layout and reference checks, and
visual review. `pdf_build.log` is the final successful LaTeX build output.
The theorem inventory counts declarations once each, including explicitly
marked infrastructure and an external metatheoretic obstruction.

**No new Lean source was compiled. No full iPRA derivation was kernel-checked
in this environment.** Computational diagnostics and document quality checks
are distinct from the human mathematical proofs and the formalization plan.

Reproduce the exact computation suites from the package root with:

```sh
python3 code/verify.py
```
