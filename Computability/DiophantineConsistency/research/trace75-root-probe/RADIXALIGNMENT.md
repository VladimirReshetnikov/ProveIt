# Trace75 radix alignment

`Trace75RadixAlignment.graph_radix_alignment` proves in any IΣ₁ model,
under β≥31, `MC<β`, `MF<2β`, an actual positive trace75 zero, and explicit
`d≥2`, `β+1=2^d`, that one positive `N` satisfies `q=2^(d*N)`,
`d*N≤rankNat`, and `v 5=2^(rankNat−d*N)`. The port `K0` is arbitrary.
This is a necessary consequence; no halt or iPRA equivalence is claimed.

`run-radixalignment-v2.py`, `observations/radixalignment-attempt01/`: Lean
exit 0, no warning/error; object
`/tmp/trace75-radixalignment-0d641wdy/Trace75RadixAlignment.olean`, SHA-256
`ab373a05258ece9a1da30257e262cf84af2d02e5adbe727bee077babeefd93c2`.
The retained first runner had a generated variable-name collision and exited
before creating an observation or launching Lean; v2 corrects it. Selected
direct imports are pinned; historical transitive/package ancestry and
external graph/file binding remain inherited limits.

The same source passed `run-radixalignment-v3.py`,
`observations/radixalignment-attempt02/`, selecting the fresh GraphPower
v3 object and pinning its first-resolved historical `ModelRatioBounds`
object (`fcf4152e49cb9a989bd9f8ba08259a26c646dfca18370b0c6e1ce7ebfb33b8a7`).
Its object at `/tmp/trace75-radixalignment-i4hl__80/Trace75RadixAlignment.olean`
is byte-identical to attempt 01. Known producer-time drift for that inherited
historical object is not repaired; a coherent fresh-provider rebuild is needed.
