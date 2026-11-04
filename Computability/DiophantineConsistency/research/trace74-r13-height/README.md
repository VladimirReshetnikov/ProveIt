# Ordered-ring height bound for a possible (10,13) pair

`Trace74R13Height.height` proves that `q≥2³⁰`, `0<h<q`, `y≥q³`, `x≥0`,
and `y⁷<32x³` imply `536870912 h y < x` in any strictly ordered
commutative ring. The factor is `8·8192²`; this is the size bound needed
to bound a quotient of the reduced projection when the main index is 13.

The theorem assumes the displayed `y⁷<32x³` estimate. It does not derive
that estimate from a Pell pair, bind it to a graph zero, establish a
projection contradiction or reverse guard, or prove an iPRA endpoint.

Lean 4.32.0 ran with `/tmp:` prepended to the captured `lean_path` field
from [`trace74-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-main-index-eleven-draft/observations/attempt01/terminal.json),
`timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as `--root`,
and output `/tmp/Trace74R13Height.olean`. Actual session 87036 exited 0;
the axiom report lists only `propext`, `Classical.choice`, and
`Quot.sound`. Two earlier author runs failed because `q³` needed explicit
product normalization.

```text
Trace74R13Height.lean   64d656608702e645177b24621dd9316f926d8b1a44d74d47b4fc8c813e07c8f2
Trace74R13Height.olean  a46433cc3b822986c80d12f248861d3a9ff1a71580db9e179f6b816720a4231e
Trace74UniformHeightContradiction.olean c994954d496b9bc17f1354d28342699e2b0e02bd91eac3f0c3333421143c159e
```

This is a captured-provider author check, not an independent replay or a
coherent current-source rebuild. Full transitive/package ancestry and
search-path selection remain unauthenticated.
