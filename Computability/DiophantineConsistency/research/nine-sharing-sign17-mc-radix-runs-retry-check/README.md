# Sign17 symbolic MC radix runs: narrow core retry

This seventeen-stage source-only attempt replays the audited symbolic provider,
then compiles a narrow generic digit core and proposes the same symbolic
low-mask run equality as the first attempt. The core adapts the short proofs
`ofDigits_map_range` from the repository's `Section4.lean` and
`ofDigits_maskList` from `LowMaskCoding.lean`, using the actual existing
`LowMaskCoding.mask`/`supportValue` definitions. It explicitly imports and
pins the Mathlib geometric-sum module rather than relying on the absent
`LowMaskCoding.olean`. A source import-graph scan found no path from GeomSum
to the earlier conflicting Matrix.Defs, but Lean compatibility remains to be
checked. The first run's broad list-length `simp` is replaced by restricted
length rewrites that do not expand the replicated lists.

The [first failure](../nine-sharing-sign17-mc-radix-runs-check/attempt01/README.md)
is independently audited. No new radix theorem, MC byte equality or Lean
file/gzip/JSON binding is claimed yet. Resource guards are unchanged. Author
no-Lean preflight exited 0. Runner SHA-256:
`4915db5c40f2bf9f2ddfc412d159cd37342afb13666df7b3b51edac82f1c2fd1`;
manifest SHA-256:
`557c00927c981d903a588f3e9ecb3b3a72571c45a14119229301f20856833cfc`;
new core/runs source SHA-256:
`022e2095457b8f0021f5079e614f0f9353a79a41af6ebcd517d65601f5dc9292` and
`a22a94127d7a9b1435416032b12d76add1a66e4c5eaf51dba3ae61c7107f8baf`.
Independent prelaunch review and an assigned Lean slot are required.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-mc-radix-runs-retry-prelaunch-independent/README.md) passed.

Attempt 01 failed with observed outer exit 1; see [`attempt01`](attempt01/README.md). The [independent failure audit](../../reviews/nine-sharing-sign17-mc-radix-runs-retry-terminal-independent/README.md) passed; the packet is frozen.
