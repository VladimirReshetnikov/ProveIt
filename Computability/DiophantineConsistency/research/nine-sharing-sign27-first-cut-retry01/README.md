# Proposed sign27 first-cut numeral retry

The only proof change adds `map_ofNat` to the N1-zero simplification, targeting the observed unnormalized `ι 2`; theorem statements, lift, imports and other proofs are unchanged. The previous N1-zero report contained `sorryAx` and is not a theorem. The reviewed retry succeeded as recorded in [attempt01](attempt01/README.md), and the [independent terminal audit](../../reviews/nine-sharing-sign27-first-cut-retry01-terminal-frontier-independent/README.md) passed. It does not assert a complete zero bridge.

The runner authenticates the same sign27/sign28 syntax and square-sum providers, 1,057 byte-matched overlays, and reviewed lift source. Author no-Lean preflight exited 0; deeper ancestry and the historical plan README-link caveat are inherited. Limits remain `-M2800`, 120 seconds per call, sampled 4-GiB RSS, 10-GiB available-host-memory floor and 5-GB disk precheck.
