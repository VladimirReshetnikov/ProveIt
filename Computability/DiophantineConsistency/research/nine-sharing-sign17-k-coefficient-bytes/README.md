# External K coefficient-recipe byte check

The read-only [checker](check.py) reads the pinned sign17 JSON, K gzip/raw
snapshot and the frozen 3297-entry doubled coefficient array from the
padding-staircase certificate. It checks that the final nonzero coefficient
index is 985 and that the unsigned big-endian raw integer equals
`r^18 + r^1004 + r^2020 + Σ c[i] r^(1005−i)` for `r = 2^47`. It exited 0;
[result.json](result.json) records the input hashes and sizes.

Checker SHA-256:
`e2f880def9fe5501d0d9515904d77ac10cdf4de114b9f5c81eb3d3a2f72636e1`;
result SHA-256:
`34f321334788707482641c54e78f9962dd59fdf54881eed8ad6269b5f772cf26`.
This is an external Python check of a frozen coefficient recipe, not a Lean
proof that the coefficient array equals `CurrentKernel2011.K`'s tile/rank
sum and not a Lean gzip/file theorem. The [independent review](../../reviews/nine-sharing-sign17-k-coefficient-bytes-independent/README.md) passed; the packet is frozen.
