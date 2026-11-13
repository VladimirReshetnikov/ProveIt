# K Fin224 weight-certificate union

This checked 22-stage attempt replays the independently audited Fin96
union and the two independently audited Fin64 weight batches for candidate
rows 96–223. It proves Fin160 and Fin224 theorems for the concatenated
index/weight vectors. The runner pins both prior receipts and verifies source
bindings; it recompiles the sources in one provider context rather than
assuming replayed objects with different hashes can be mixed. The candidate
row labels are not established physical ranks, and remaining rows, ordering,
full K and external file binding remain separate. Usual per-child limits
apply. Author no-Lean preflight exited 0.

Runner SHA-256:
`b153ff3a7c33051dc310943680d9f35f470acbe5adfa5fbc8f87acec95ebf9a4`;
manifest SHA-256:
`fdc211839a5ddeb41cb4e4508993db28d6a581c3586e8cae6794e19682ca332e`;
new source SHA-256:
`551880409b6a534d71d5f2d5f437085acbc5f8550395e7fd8f461f73bd9997f8`.
The run used the established independent-review and exclusive-slot workflow.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-weight-union224-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-weight-union224-terminal-independent/README.md) passed; the packet is frozen.
