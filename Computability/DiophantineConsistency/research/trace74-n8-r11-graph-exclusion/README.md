# Same-zero exclusion of first index 8 and main index 11

`Trace74N8R11GraphExclusion.graph_impossible` proves in every model of
`IΣ₁` that one tuple cannot simultaneously have all witnesses positive,
its first port positive, `q≥2³⁰`, a zero of the actual 74-operation graph,
and its first and main Pell ordinate equations at indices 8 and 11.

For the same tuple, the proof invokes the checked first-8/main-11 Pell
height, derives `512b<Y`, specializes the reduced graph projection at
`2^(11−2)=512`, and applies the uniform bounded-quotient contradiction.
It does not assume a reverse guard or derive an iPRA endpoint. This lemma
only excludes the single pair; a separate client is needed for arbitrary
first indices `n≥8`.

Lean 4.32.0 author check session 86308 exited zero without warnings; its
sole axiom report was `[propext, Classical.choice, Quot.sound]`. It used
`timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as `--root`,
and `/tmp/Trace74N8R11GraphExclusion.olean` as output. `LEAN_PATH` used
`/tmp` followed by the captured provider sequence from the [uniform
reduction record](../trace74-uniform-projection-reduction-draft/README.md).
The earlier check exited with an error on abstract numeral subtraction;
the final source proves that subtraction using explicit cancellation.

```text
source         98c97e2e06dc118408ed4d81dea67a88dd1c48fa1a9a4cdc6953e116c1e4b99e
output         08f862eec2ff5728c26d70e1e4fa3b6fdb341195e8578a0506d8c1537fe2bd8b
tuple height   e2cea22621830b88f0939b38727332cf31dda2cf7f8423a7711e5485b907366d
quotient size  52d28e8caf16d04aeebdbf52e115e06237c2782a117f1378eb4eae0f6538ccf6
projection     e7e72f7339c7f5c2d876b82c0ac4ed84aac32a0c9a01b80291e52904eb4cc92c
```

The check uses temporary captured providers; it is not an independent
replay or a coherent current-source rebuild, and complete provider and
package ancestry were not authenticated.
