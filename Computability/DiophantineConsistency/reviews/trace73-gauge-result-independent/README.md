# Independent result review: trace73 gauge

**PASS.** The accepted source proves four all-commutative-ring identities
for arbitrary ring ports p, valuation v and t. With h=p₀v₀, q=h+1 and
s=(p₁+v₅)q+1, the move changes only `v₁ → v₁+h*t`,
`v₂ → v₂+h²*t`, and `v₇ → v₇−s*t`. It preserves rank, sends
`B → B−h*s*t`, preserves the centered carrier and preserves the actual
literal trace73 evaluator. Inspection confirms these expressions match the
actual register and literal/center definitions. The identities do not prove
positive natural coordinates, exhibit a graph zero, prove a converse, or
establish an iPRA endpoint.

Accepted `research/trace73-gauge/observations/attempt04/terminal.json` has
SHA-256 `8948683f35f6d24bfd6abdeadcd7a89c239b263d57a7b9d5fdfb18d27761e66d`;
the regular object `/tmp/trace73-gauge-r0w9s5ez/Trace73Gauge.olean` has
SHA-256 `397b4aec0c8ed0042867e0e24cb0cc479213769262bda2248b9fccc9d76e7ca9`.
The source, copies, runner, all four exact `[propext, Quot.sound]` reports,
seven selected provider pins, first direct import and resource samples were
checked. Attempts01–03 contain errors and `sorryAx` and are excluded. Tool
exit 0 is author-reported; there is no separate outer receipt or independent
Lean replay. Full transitive, historical, package and dynamic ancestry remain
outside this review.

`check.py` SHA-256 `fdba4c32304b8b1990c179197ed42cdd3a034f2a0592b4ed8ab1e1935409c4b6`;
`result.txt` SHA-256 `a849cd38f1b590604b997293d9ed2f774129cd8cd40f3fba0bfee02580994050`.
