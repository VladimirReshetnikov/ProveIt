# ProveIt integration notes

Suggested new directory, without overwriting predecessor artifacts:

```text
Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/
  color-coded-affine-partitions/
```

The directory should remain in the research tier until the geometric proof and its formalization boundary have been reviewed. No index number is reserved here; assign one according to the repository state at integration time.

## Proposed index entry

**Color-Coded Affine Partitions: Exact Boundary Saturation and a Two-Term Growth Law.**
Proves exact point–torus-bound attainment for products of coordinate crosses in explicit and asymptotically near-critical regions. For each fixed prime power q>2, the regularized cost is `(q-1)s-log(q-1)/log(q/(q-1))+O_{q,epsilon}(s^(-1+epsilon))`, with sharp centered-error exponent -1. Includes self-contained ordinary proofs, exact finite certificates, rational budget checks, and a theorem-status ledger. Not proof-assistant verified; no global Szemerédi claim is used or asserted.

## Recommended integration checks

Run `make verify`, `make numeric`, and `make pdf` from this directory. Verify `SHA256SUMS` before making local edits; the checksum file will naturally need regeneration after edits or PDF rebuilds.

Preserve the existing torus-defect manuscript and its integration note. Its defect/Jensen estimates are credited prior tools, not superseded claims. Add a cross-link describing the new regime as **fixed q, growing s**, rather than claiming an improvement to the old fixed-s, growing-q error term.

Archive the explicit certificate files and the JSON results with the source. The code relies on no network services and performs no persistent repository changes. The main finite checker uses only the Python standard library. The approximate transcendental evaluations use mpmath 1.3.0 in the tested environment.

## Trusted boundary

Do not promote the manuscript to a “Lean verified” result merely because the Python checks pass. A future Lean development must prove that the constructed cells are affine, disjoint, and cover the whole cross product, not merely formalize the final numerical inequality.

No theorem from the `openai/math` arithmetic-progression family is imported as a mathematical dependency. No entire repository was independently audited. No git commit, branch, pull request, or remote file change was made in this delivery.
