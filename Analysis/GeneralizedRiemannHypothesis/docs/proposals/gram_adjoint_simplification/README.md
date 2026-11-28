# The integral adjoint without a tight frame

A proof-simplification proposal for the readable Alpöge–Claude Dirichlet GRH development, not an independent proof of RH. The proposed replacement uses the existing Weyl–Fock identity `G H = h I` and paired-conjugate dual norms to eliminate the specialized tight-frame construction in the one-lift comparison-operator argument. It also permits the normalization `n_aut h` instead of `n_aut h²` while preserving all downstream estimates.

## Files

- `gram_adjoint.pdf` and `gram_adjoint.tex`: mathematical report and standalone LaTeX source.
- `LEAN_PLAN.md`: concrete formalization and integration plan (not compiled Lean code).
- `check_gram_adjoint.py` and `checks.txt`: exact rational-matrix and number-field regression tests and recorded output.
- `source_audit.tsv`, `proposal_audit.tsv`: source anchors and nonduplication audit at the pinned ProveIt revision.
- `verify_sources.py`: optional verification of source and proposal blob/tree IDs in a local Git checkout.

## Reproduction

```sh
latexmk -pdf -halt-on-error gram_adjoint.tex
python3 check_gram_adjoint.py
python3 verify_sources.py /path/to/ProveIt
```

The verifier uses `git` and the pinned commit `cdecfeba5d834fbf2f97de71cc7766b58ec4520e`. It is supplied for local reproduction and was not run against a full checkout in this session. The source and proposal hashes were retrieved using the GitHub connector. The exact finite tests were run; they are not a substitute for the mathematical proofs. The PDF was compiled and inspected. No Lean executable or local project cache was available, so an integrated Lean replay and measurement of code savings remain outstanding. No GitHub files were changed.

The independent verification record for the upstream baseline is https://math.mit.edu/~drew/shortgrh/ . That verification does not cover this proposed substitution.
