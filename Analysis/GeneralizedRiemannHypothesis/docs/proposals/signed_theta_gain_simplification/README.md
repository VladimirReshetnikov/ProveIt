# Signed local gains and cheaper colength

A paper-level simplification of the arithmetic assembly in the readable theta-lift proof of RH and Dirichlet GRH. It separates the local loss of divisibility from the local colength cost and replaces the global rounded rational normalization with a signed comparison of one fixed determinant. The proof reuses the deep inputs in the source, and is compatible with the five proposal folders inspected at the pinned revision.

## Files

- `signed_theta_gain.pdf`: compiled mathematical report.
- `signed_theta_gain.tex`: complete LaTeX source, including linked source anchors.
- `FORMALIZATION.md`: staged Lean integration plan; specifications, not compiled Lean code.
- `check_gain_accounting.py`: exact rational regression checks; standard library only.
- `checks.txt`: actual test results.
- `source_anchors.tsv`: selected source declarations and immutable Git blob identifiers from the GitHub connector.
- `proposal_audit.tsv`: five existing proposals, source locations and overlap assessment.
- `verify_sources.py`: checks source file blob hashes and declaration anchors in a local checkout.

## Reproduction

```sh
latexmk -pdf -halt-on-error signed_theta_gain.tex
python3 check_gain_accounting.py
python3 verify_sources.py /path/to/ProveIt
```

The intended checkout is commit `89d12dd40424f1217fd818d84877b3da52396a3b`. The source verifier requires a local checkout; it was not run against one in this session. The connector was used to read the selected files and obtain their hashes and locations. No repository files were modified.

## Scope and status

The new local colength budget is at most `150 f a log b` per full source dimension. Under the existing scale, spanning and completion hypotheses, the new comparison yields `m R ≤ (1 + O(1/log b)) f a (log b)^4`, and in particular `m R ≤ 2 f a (log b)^4` for sufficiently large admissible scales. Keeping the old normalization also gives the improved asymptotic bound with a small extra rounding term. The new upper-bound assembly depends on the original lower determinant height, local divisibility, and other deep results. It is not an independent RH proof, a completed Lean refactor, or an exhaustive re-verification of the original Lean project. The finite checks are illustrative regression tests; the universal proofs are in the report. LaTeX was compiled and the PDF visually inspected.
