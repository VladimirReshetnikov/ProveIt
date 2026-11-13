# Variable-width lower power comparison in arithmetic models

`Trace74VariableWidthSizeModel.lower_power_bound` proves in any model of
`IΣ₁`, at arbitrary internal `B,m,c,r,e`, that

```text
power 2 (5c) * power h c * power K (2c) ≤ power Y (m+1)
```

provided `power 2 B≤q`, `q³≤Y`, `h≤q`, `K=power 2 r`,
`r≤n+c`, `e+c=3(m+1)` and `2c(n+c)+5c≤B e`, where
`n=m+3c+1`. The inequality is deliberately **nonstrict**. The two equations
avoid model subtraction; in the integer argument they encode
`m+1=n−3c` and `e=3n−10c`. The arithmetic threshold is a sufficient
condition and is not asserted to hold for any graph valuation here.

The proof combines represented `power_add`, `power_iterate`, base and
exponent monotonicity. It needs no new induction over model indices. This
lemma does not derive the Pell gap, size, threshold or index hypotheses
from a 74-operation zero; it does not establish the reverse guard or an
iPRA endpoint. The preceding variable-width Pell upper estimate is a
separate conditional theorem.

The author check used:

```text
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-variable-width-size-model \
  Computability/DiophantineConsistency/research/trace74-variable-width-size-model/Trace74VariableWidthSizeModel.lean \
  -o /tmp/Trace74VariableWidthSizeModel.olean
```

Actual session 54013 exited 0 without warnings and reported only `propext`,
`Classical.choice`, and `Quot.sound`. SHA-256: source
`6a97cbfac1653f4659ec9f1aab221840ff979d1af28b66ece0bb96cdfc7a9821`,
output object
`fc0532e0990dedf3186b797ae783740702ec345fc1000d3b5f615970504c27d5`,
imported `Trace74VariableWidthPellHeight.olean`
`3957186ad270213a2ae188e718eb91d2aac7895035063aed8ac6ab0b135cb6e4`,
Lean executable
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Temporary providers and transitive/package/dynamic/search-path ancestry
are not independently authenticated; this is not a clean current-source
build or independent replay.
