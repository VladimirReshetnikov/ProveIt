# Adjacent-weight criterion for the actual K physical map

This checked 18-stage attempt replays the independently audited actual
physical-map criterion and replaces its global descending-weight
hypothesis with 940 adjacent inequalities among the 941 nonzero positions.
It imports and pins `Mathlib.Order.Fin.Basic` and uses its finite strict
antitonicity criterion. Candidate zero/nonzero behavior and all adjacent
inequalities are still explicit assumptions; no concrete candidate rank,
complete K, external file binding, or consistency equivalence is claimed.

The usual per-child resource limits apply. Author no-Lean preflight exited 0.
Runner SHA-256:
`30ba257f969df82853daf70fbdfccaf679cdca2cad07f573c2f236e90f69eff2`;
manifest SHA-256:
`eb40db586db5302de5b47f10bc3880a547fd47d9f07892b724c12c7c25be7313`;
source SHA-256:
`f7389f2679588fc0eb11cb6568a4e135d640b46fbedfe42020d7d01c4b5211e2`.
The run used the established independent-review and exclusive-slot workflow.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-adjacent-rank-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-adjacent-rank-terminal-independent/README.md) passed; the packet is frozen.
