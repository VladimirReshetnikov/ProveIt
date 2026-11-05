# Independent review: current14 beta is nonzero

**PASS within fresh-base captured-provider scope.** The checked
[`Current14BetaNonzero.lean`](../../research/rational-carrier64-current14-actual-port-split/Current14BetaNonzero.lean)
proves the integer-valued `CurrentWindowCarry2011.ports 0` is nonzero.
The fixed source definitions give `radix=2^47`, `beta=radix^2011−1`
as a natural number and `ports 0=(beta:ℤ)`. The proof evaluates only the
small radix inequality `1<2^47`, then uses the general `one_lt_pow₀`
lemma for exponent 2011 and `Nat.sub_pos_of_lt`, finally casting nonzero
to ℤ. It does not numerically expand the full 94,517-bit beta. This is
the current14 beta, distinct from the compact44 beta used elsewhere.

The retained beta01 result/log match their temporary originals and record
Lean exit 0, no stop and the expected axiom report. The output object and
the directly imported fresh-base `CurrentKernelData2011` and package
`Mathlib.Tactic.NormNum` objects match their pins. Independent
[check.py](check.py) ran exit 0 and rechecked all 35 direct, companion and
shadow guards; it also verifies the pinned fresh-base state/manifest, the
successful `CurrentKernelData2011` and `CurrentMaskData2011` producer
records, source snapshots and workspace source hashes, direct inputs and
logs. [result.json](result.json) records the check. The MaskData object is
an inherited dependency, not a direct import guarded during beta01. No Lean
replay or complete transitive/dynamic ancestry audit was run; sampled
monitoring limits remain inherited. This theorem alone proves no rational
zero equivalence or iPRA endpoint.

Checker SHA-256
`c19c1fd839e084754cf08134a4e89fcc125147cd035d64c6b02c6e090556c947`;
result SHA-256
`369a13aa9fc9be626acd4bb0e949a3dae5dd347e9732a985f82f449852787a88`.
