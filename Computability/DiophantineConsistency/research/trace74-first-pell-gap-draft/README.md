# Guard-independent first-Pell gap

`Trace74FirstPellGap.graph_first_pell_gap` derives from the actual positive trace74 graph zero, positive beta, positive valuation, and the stated arithmetic-model assumptions, the dichotomy

```
k = 8P+4  or  32P²+32P+6 ≤ k,    P = X Y².
```

It uses the same first-Pell index supplied by the checked recurrence and the checked lower bound `n≥2`: index 2 gives the first value exactly; every index at least 3 gives at least the second value by strict ordinate monotonicity. It requires neither an F/C bound nor a reverse guard. The index used here is the first-Pell index, distinct from the odd second-Pell index.

The reviewed author check passed in actual tool session 30067, outer exit 0; terminal `observations/attempt01/terminal.json` SHA-256 `ced3ef1098b4bcb3bb36dbfe8e333f6fb817528bf4bbc131ab1c643d4f4cea18`, object `/tmp/trace74-first-pell-gap-qzq0p2k0/lib/Trace74FirstPellGap.olean` SHA-256 `663537c7e79b33270b7a2fb0689ba803c4e8d292eced26c2dff27fba5387fb1f`. The one named axiom report was clean. Independent [result audit](../../reviews/trace74-first-pell-gap-result-independent/README.md) passed, SHA-256 `c0f0fa42682a455a1b2a941b57fee2a52d532f11459d6920780b52bbdc991547`. Direct-pin/search-path and inherited project/package/dynamic ancestry limits remain.

[Source review](../../reviews/trace74-first-pell-gap-draft-independent/README.md) and [scoped prelaunch review](../../reviews/trace74-first-pell-gap-prelaunch-independent/README.md) are recorded separately.
