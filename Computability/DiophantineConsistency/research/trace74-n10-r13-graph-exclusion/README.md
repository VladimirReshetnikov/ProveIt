# Same-zero exclusion of indices 10 and 13

`Trace74N10R13GraphExclusion.graph_impossible` proves in every model of
`IΣ₁` that a positive 74-operation graph zero with `q≥2³⁰` cannot have
both its first and main Pell ordinates at indices 10 and 13 for the same
tuple. The first port is positive; the other ports are arbitrary.

The proof combines the same-tuple height bound with the actual reduced
graph projection and the variable-parameter quotient obstruction. It does
not establish general absence of zeros, a reverse guard, 74/75 equivalence,
or an iPRA endpoint. The external payload-to-symbolic-port link is also
outside this result.

The Lean 4.32.0 author check used `/tmp:` prepended to the captured
`lean_path` field from
[`trace74-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-main-index-eleven-draft/observations/attempt01/terminal.json),
`timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and output `/tmp/Trace74N10R13GraphExclusion.olean`. Actual
session 47664 exited 0 without warnings; the report lists only `propext`,
`Classical.choice`, and `Quot.sound`.

```text
Trace74N10R13GraphExclusion.lean  09a7f8424e92c34a3340805a78bc8f9a1a111b4b55efc7662db87e7d378d030d
Trace74N10R13GraphExclusion.olean a16bc0ffcf0b8905d8caa01af667a3e77a9a93bcf9aabc041072b75bc98a787c
Trace74N10R13ModelHeight.olean    7a34eef8ce70dc67a2eb7d49772d53aaa100dcb51def96ba7daa5aea7d95f0c4
Trace74UniformProjectionGraph.olean e7e72f7339c7f5c2d876b82c0ac4ed84aac32a0c9a01b80291e52904eb4cc92c
Trace74UniformQuotientSize.olean   52d28e8caf16d04aeebdbf52e115e06237c2782a117f1378eb4eae0f6538ccf6
```

This captured-provider author check is not an independent replay or a
coherent current-source rebuild. Full transitive/package ancestry and
search-path selection remain unauthenticated.
