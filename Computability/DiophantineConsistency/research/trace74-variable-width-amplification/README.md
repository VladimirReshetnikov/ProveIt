# Variable-width height amplification in arithmetic models

`Trace74VariableWidthAmplification.amplified_height` proves in every model
of `IΣ₁`, for arbitrary internal `m,c`, that the two explicit hypotheses

```text
2*power Y (m+2c+1) < power 2 (2c)*power X c,
power 2 (5c)*power h c*power K (2c) ≤ power Y (m+1)
```

imply `8hK²Y²<X`. Powers are represented model powers. The first bound is
strict, the second is nonstrict, and no positivity premise on `c` is
needed. The proof uses addition and iteration of represented powers,
monotonicity, and cancellation of the positive power of two.

The hypotheses have separately checked conditional model derivations in
[`trace74-variable-width-pell-height`](../trace74-variable-width-pell-height/README.md)
and [`trace74-variable-width-size-model`](../trace74-variable-width-size-model/README.md).
This lemma does not derive them from a graph zero, prove an index window,
establish the reverse guard, or supply an iPRA endpoint.

The author check used:

```text
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-variable-width-amplification \
  Computability/DiophantineConsistency/research/trace74-variable-width-amplification/Trace74VariableWidthAmplification.lean \
  -o /tmp/Trace74VariableWidthAmplification.olean
```

Actual session 41195 exited 0 without warnings and reported only `propext`,
`Classical.choice`, and `Quot.sound`. An earlier exit-0 run had style
warnings; the final source removes them. SHA-256: source
`edb3c6b4fa1617b9fdca38fa991ba477369cf24d0fcc871f03613767bda99082`,
output object
`b2eb228fa7811228d64993dacf68a3703d703b555d14677fb3da934f24747a52`,
imported `Trace74VariableWidthSizeModel.olean`
`fc0532e0990dedf3186b797ae783740702ec345fc1000d3b5f615970504c27d5`,
Lean executable
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Temporary providers and transitive/package/dynamic/search-path ancestry
are not independently authenticated; this is not a clean current-source
build or independent replay.
