# Generic high-mask interval-sum formula

`BFSHighFlat.runs_high` identifies the generic run shape with the existing `CompactHighPopulation.highDigits` when its three weights are set to `mu`, `padding` and `lastPadding`. `BFSHighFlat.expansion` proves the full weighted formula at an arbitrary natural radix `B` and arbitrary weights `a`, `b`, `c`:

```text
4 + Σ_{1013≤j<1023} B^j + Σ_{1065≤j<1074} B^j + B^2195 + B^3296
  + a*(B^4393+B^5495) + b*Σ_{8792≤j<8805} B^j + c*B^8805.
```

This uses the [checked generic run expansion](../ten-positive-80-bfs-high-runs/README.md) and converts the three shifted geometric sums to interval sums. It does not evaluate the enormous fixed-radix value. The fixed `highNat` specialization, iPRA port transport and PDF/file semantics remain separate.

Guarded author `observations/attempt01/` and its enclosing tool session exited 0. Source SHA-256 is `888308a57a6c5dd2c018f680f8c36d14577d97448c82d764dca46e0389c80f81`; terminal SHA-256 is `35cf26f4ce4fb1c94606a5c29258a8f62107cc3b27aa4b50bb367874e1c87fa2`; output `/tmp/bfs-high-flat-ygaljyep/BFSHighFlat.olean` SHA-256 is `7bd984120f153d8487ea147c7cfc48e7cebad2a410be8fd2170c9f99864c368d`. The direct run-expansion provider and selected inherited objects are pinned; full historical-source, transitive package and dynamic ancestry remain inherited. No independent Lean replay is claimed.
