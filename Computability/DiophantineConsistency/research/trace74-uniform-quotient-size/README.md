# Variable-parameter quotient-size contradiction

`Trace74UniformQuotientSize.impossible` proves in a discretely ordered
ring that the reduced projection divisibility is impossible when `h>0`,
`Y≥1`, `L≥1`, `Lh<Y`, and `8h(4L)²Y<X`. It bounds the reduced numerator
above by `32h(4L)²Y³`, uses the explicit bound on `X` to show the divisor
times `Y` is larger, and applies the preceding bounded-quotient obstruction.
The parameter `L` is arbitrary and need not be a standard numeral.

The theorem assumes both the divisibility and the size bounds. It does not
derive them for a graph zero, settle the reverse guard, or prove an iPRA
endpoint.

The Lean 4.32.0 author check used `/tmp:` prepended to the captured
`lean_path` field from
[`trace74-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-main-index-eleven-draft/observations/attempt01/terminal.json),
`timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and output `/tmp/Trace74UniformQuotientSize.olean`. Actual tool
session 1423 exited 0 without warnings; its axiom report lists only
`propext`, `Classical.choice`, and `Quot.sound`.

```text
Trace74UniformQuotientSize.lean     fc552b69272ff581caaeab0ccfdd6fbab913cb79895eeeea622fa721175e7e9b
Trace74UniformQuotientSize.olean    52d28e8caf16d04aeebdbf52e115e06237c2782a117f1378eb4eae0f6538ccf6
Trace74UniformBoundedQuotient.olean  e217b2d6913b1056bc8b4257e31bf9727e2da3984813dfa355f448598f811708
```

This captured-provider author check is not an independent replay or clean
current-source build; full transitive/package ancestry and search-path
selection were not authenticated.
