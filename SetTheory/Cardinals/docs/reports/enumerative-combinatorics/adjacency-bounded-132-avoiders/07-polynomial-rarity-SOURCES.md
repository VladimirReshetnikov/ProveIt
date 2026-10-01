# Source ledger and research boundary

Inspection date: 30 September 2026. Repository reads used the connected GitHub tool; public research sources were checked on the web. The snapshot below pins the repository rather than an indefinitely moving main branch.

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned **commit**: `ffddaa8b9c89e7bf027e1442cc6216bb010906d0`
Commit timestamp returned by GitHub: 2026-09-30T23:38:21Z.
Root tree of that commit: `cb9c68b0259260775183086b191db520ccb3e0ff`.

The initial `/git/trees/main?recursive=1` request returned the root-tree identifier `f4457a1d19701d32e8f324240c497653d235b53e`. That is NOT a commit identifier. Initial file reads used that reference. The relevant README and both code-file blob identifiers were subsequently confirmed at the pinned commit above. The moving branch was receiving other manuscripts while this work was being prepared.

Relevant directory:

    SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders/

### README.md

Blob: `a40d20342fcaf1a97c18ea0064b9c0c9bd9d694e`

https://github.com/VladimirReshetnikov/ProveIt/blob/ffddaa8b9c89e7bf027e1442cc6216bb010906d0/SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders/README.md

Read to identify the report's results, status, and unresolved regimes. In particular, its "Not claimed" section explicitly leaves lower-half equivalents/hierarchy and the order and window at n/2 unresolved. It records the upper-half profile used only for comparison in the article. Its status statement describes the reports as AI-assisted and unrefereed, without Lean or Rocq formalization.

We did not read or independently audit the entire approximately 140-page combined report. Our proof does not use its asymptotic theorems. No claim is made that all incoming, unmerged, or simultaneous reports have been exhaustively checked for duplication.

### code/model.py

Blob: `aee5528c72552036b5e630bd49afe2715f440da4`

https://github.com/VladimirReshetnikov/ProveIt/blob/ffddaa8b9c89e7bf027e1442cc6216bb010906d0/SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders/code/model.py

Read in full. It contains the endpoint recurrence, `majorant_counts`, and the first-deficiency skew-block lower construction `block_counts`. The article's two envelopes are rederived from these elementary constructions; they are not claimed as new.

### code/05-macroscopic-deficits-model.py

Blob: `f0248e0d6181200257e2949c1a8fa8f9fecf5617`

https://github.com/VladimirReshetnikov/ProveIt/blob/ffddaa8b9c89e7bf027e1442cc6216bb010906d0/SetTheory/Cardinals/docs/reports/enumerative-combinatorics/adjacency-bounded-132-avoiders/code/05-macroscopic-deficits-model.py

Read in full. The delivered `EndpointCounter` adapts its exact endpoint recursion and unrestricted shortcut, with a separately packaged verification suite. The article provides a direct derivation. The code is a finite verification instrument, not an analytic theorem prover.

## Public primary literature

1. Nathaniel Nadler, *On 132-Avoiding Permutations with an Adjacency Constraint*, arXiv:2604.22135v1, 24 April 2026.
   https://arxiv.org/abs/2604.22135v1
   The arXiv record was checked for the definition, maximum-position restriction, and original fixed-bound problem.

2. Teruki Mayama and Dai Akita, *Finite-state enumeration of adjacency-constrained 132-avoiding permutations*, arXiv:2605.23519v1, 22 May 2026.
   https://arxiv.org/abs/2605.23519v1
   The arXiv record was checked for the endpoint-state method and fixed-bound results. The exact recurrence used here was read from the credited repository implementations and rederived in Appendix A.

3. Céline Kerriou and Peter Mörters, *The fewest-big-jumps principle and an application to random graphs*, Bernoulli 31(3), 2525–2543 (2025), DOI 10.3150/24-BEJ1816; arXiv:2206.14627.
   https://arxiv.org/abs/2206.14627
   https://doi.org/10.3150/24-BEJ1816
   The record and an author-hosted PDF were inspected, including the theorem assumptions. This is related context, not an invoked theorem: it treats a growing number of independent truncated summands, whereas our proof is a local subcritical renewal calculation. The manuscript does not claim to invent the fewest-big-jumps mechanism.

Targeted searches considered adjacency-constrained 132-avoiders, macroscopic bounded adjacent jumps, and truncated heavy-tail/fewest-big-jumps asymptotics. These were not an exhaustive priority search.

## New assertions and verification status

The substantive assertions developed in this package are the uniform local renewal comparison for 0 < alpha < 1, its permutation transfer, the complete fixed-fraction polynomial-order staircase (including reciprocal endpoints), and the order-crossover scales. Proofs are written in the manuscript. No external theorem is used to infer those assertions from finite data.

The exact finite tests and output CSV files are reproducible; their scope is explicitly limited. Plotted and tabulated decimals are rounded, not certified intervals. Exact amplitudes, limiting crossover functions, conditioned-permutation geometry, and uniformity as q grows are left as research questions. Independent mathematical review and formal verification remain outstanding.
