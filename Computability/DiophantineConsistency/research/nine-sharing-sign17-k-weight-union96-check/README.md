# First K Fin96 weight-certificate union

This checked 19-stage attempt replays the independently audited Fin32
weight probe for witness rows 0–31, the Fin64 batch for rows 32–95, and the
generic `Fin.append` certificate theorem. It proves a single Fin96 theorem
for their concatenated candidate-index and weight vectors. The runner pins
each of the three terminal receipts and checks source bindings before replay.
The candidate positions are not yet proved physical ranks. Remaining table
rows, ordering, complete K, and external file/gzip binding remain separate.
The same per-child resource guards apply. Author no-Lean preflight exited 0.

Runner SHA-256:
`5b74852fcb1e6be8191e4f155416e339d8723b1e9d5d5af8646e61285b18697c`;
manifest SHA-256:
`5782835b1e1c4d72f027dd6a426a77eb78e73eff4dbca73c2888a9f60c6de0b7`;
new source SHA-256:
`9dc369f5c71307959af586d830613439131022bddf6215515250127e34be0160`.
The run used the established independent-review and exclusive-slot workflow.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-weight-union96-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-weight-union96-terminal-independent/README.md) passed; the packet is frozen.
