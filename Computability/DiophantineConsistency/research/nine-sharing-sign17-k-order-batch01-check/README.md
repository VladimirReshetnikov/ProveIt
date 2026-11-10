# K candidate index and adjacent-weight sample: rows 32–95

This checked 17-stage attempt replays the independently audited Fin64
weight batch for candidate rows 32–95, then proves that its 64
candidate indices are nonzero and its 63 neighboring numeric weights strictly
decrease, and to transfer those inequalities to actual Lean tile weights.
The comparisons within this one block do not establish cross-block ordering,
the other candidates, concrete physical ranks, complete K, or external file
binding. Per-child resource guards are unchanged. Author no-Lean preflight
exited 0. Runner SHA-256:
`d364f2e73e4e4b61e9cba33bc0ec2798efc51407131f381cad9b8f15fc66840e`;
manifest SHA-256:
`e2f5907ab484f440c22fdbc065fab3912bbd5ec9d0f4ceb1e7c0d9f86f019abd`;
source SHA-256:
`18ec90133f00a35075f37904a222840f2f3e348dd15c40d9da1f1c31d7f43684`.
The run used the established independent-review and exclusive-slot workflow.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-order-batch01-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-order-batch01-terminal-independent/README.md) passed; the packet is frozen.
