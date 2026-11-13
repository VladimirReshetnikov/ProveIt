# K control block sum assembly

This source-only three-stage client recompiles the independently audited
symbolic-block and generic shifted-sum-split sources in the audited ranked
rawWord provider context. It proposes to split the six symbolic blocks,
remove zero gaps, identify their sum with the actual four control sums and
transfer that identity to the in-Lean Fin44 literal vector. The two prior
terminal receipts and source hashes are pinned. External array/file binding,
full coefficient aggregation and sentinels remain separate. Corrected Init,
one-thread and per-child resource guards are retained. Author no-Lean
preflight exited 0.

Runner SHA-256:
`0a43fc37a0dacd5b1fd26c86acb64b4fc3717083f40b91b8571a32e66c5a651f`;
manifest SHA-256:
`6a781ae8d11840d03678b86bcaa04d9f0d1ad5f93a82e1b0f0e71d663b0cec2e`;
final source SHA-256:
`08a88e2b0cdf7b27dc0b2d53e7203574bf0f0bc3c4d343d882ad68d1d80c25cc`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-control-block-sum-prelaunch-independent/README.md) passed.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-k-control-block-sum-terminal-independent/README.md) passed; the packet is frozen.
