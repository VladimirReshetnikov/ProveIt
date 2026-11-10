# Generic `ofDigits` finite power-sum bridge

This source-only one-stage client proposes, for arbitrary natural base and
finite vector, that `Nat.ofDigits` of `List.ofFn` equals the corresponding
finite sum of coefficient-times-base-power terms. It imports the audited
Fin942 provider as the established environment; it does not yet address
coefficient reversal, the exponent-1004 sentinel collision, radix bounds,
specific K digits or any external file binding. The corrected provider/Init,
one-thread and per-child guards are retained. Author no-Lean preflight exited 0.

Runner SHA-256:
`32ccf992e0fc94deb18302637c0d12e5a83d4efaf5e8b9b4f24c2b20d0847347`;
manifest SHA-256:
`b8bd4faf60ff856fac97a7a0e85883fa7b7da2553a2a3c23a794aa7cbf4778da`;
source SHA-256:
`24db7a05aa39ebf697af1bbb10c2b3bc22dc470a4bf69c99a92897aef3720098`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-ofdigits-sum-prelaunch-independent/README.md) passed.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-k-ofdigits-sum-failure-independent/README.md) passed; the packet is frozen.
