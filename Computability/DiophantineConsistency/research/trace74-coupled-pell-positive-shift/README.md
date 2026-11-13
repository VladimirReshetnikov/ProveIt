# Selecting a positive trace coordinate by shifting the Pell orbit

`Trace74CoupledPellPositiveShift.positive_T_with_shift` removes the
explicit quotient-size premise from the preceding
[Pell-to-T join](../trace74-coupled-pell-t-join/README.md). In every
`IΣ₁` model it sets

```text
f=xcoord (2t) a,   s=f(N+c),
Q=oddQuotient (2(j+t(2s+1))) (I−2),
```

and constructs an internal `T>0` with `Q+c=f(cT+N)`. The stated
hypotheses retain `t>0`, `I≥2`, `c>0`, the strong norm,
`c|I`, `c|t`, `c=ycoord (4j+1) a`, the residue of `N` modulo `c`, and
`f≡1 (mod c)`. The choice of `s` and the internal odd-quotient growth
bound supply the required size inequality.

No graph witness, norm/divisibility construction, rank CRT, external
payload binding, full 74 zero or iPRA endpoint follows from this theorem
alone.

The Lean 4.32.0 author check used `LEAN_PATH=/tmp:` followed by
`/tmp/trace74-direct-four-block-1zltaw2f/lib` and
`/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`, `timeout 120`,
`-M3000 -j1 -DElab.async=false`, this directory as `--root`, and output
`/tmp/Trace74CoupledPellPositiveShift.olean`. Actual session 13743 exited
0 without warnings and reported only `propext`, `Classical.choice`, and
`Quot.sound`.

Source SHA-256:
`0348950c83bb752a6266e654418029f9933107b86ab284b5da35348f6da027e6`.
Output object SHA-256:
`1f0d8d2a712f8c995dbba5af95db30f9f6f477ce94a90ac9f6cb9a4f2ca89383`.
Direct imported `Trace74AuxQuotientGrowth.olean` SHA-256:
`eab2a365d8486f28d6f1de64895f5bf09c9ab3350cc552ae6fcc3791135b1663`.
Temporary captured providers, full transitive/package/dynamic ancestry and
search-path selection are not independently authenticated. This is not a
coherent current-source rebuild or an independent replay.
