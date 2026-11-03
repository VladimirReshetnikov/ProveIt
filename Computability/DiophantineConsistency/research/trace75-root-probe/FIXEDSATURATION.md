# Trace75 symbolic compact-mask saturation

`Trace75FixedSaturation.graph_fixed_saturation` proves in any IΣ₁ model
that symbolic natural equalities `p0=betaNat`, `p2=lowNat`, and
`p3=betaNat+highNat`, together with an actual positive trace75 zero, yield
one `N>0` with the 67×8807 repunit/radix, the population lower bound, and
both no-carry conditions for the compact symbolic masks. The remaining
`K0` port is arbitrary. This is a necessary model condition, not a proof
of machine halt, a literal PDF/file binding, or an iPRA equivalence.

Accepted `run-fixedsaturation-v2.py`, `observations/fixedsaturation-attempt02/`:
Lean exit 0, no warning/error; object
`/tmp/trace75-fixedsaturation-sblmywo4/Trace75FixedSaturation.olean`, SHA-256
`9ee977a04a2623fd6e7d5701a62ac2dc324158141ea5b708880d68668fdec0eb`.
Attempt 01 failed before elaboration because its old symbolic-bound provider
needed an absent graph-specific transitive object; v2 uses the new compact
fixed-bound provider instead. Direct imports and first-resolved historical
`ModelRatioBounds` are pinned; known producer-time drift, a coherent
fresh-provider rebuild, full transitive/package provenance and external
graph/file binding remain open.
