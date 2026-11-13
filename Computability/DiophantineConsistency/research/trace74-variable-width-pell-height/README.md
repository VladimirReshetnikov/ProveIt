# Variable-width Pell height in arithmetic models

`Trace74VariableWidthPellHeight.lean` proves a model-indexed Pell height
estimate with an **arbitrary internal width** `c`, not just a fixed
standard numeral. In any model of `IΣ₁`, under `X≥2`, `Y≥1`, and `s≤m+4c`,
the explicit strict Pell gap

```text
(2Y) y_(m+3c+1)(2(XY²−1)+1) < y_(s+1)(Y(X+1)−1)
```

implies

```text
2*power Y (m+2c+1) < power 2 (2c)*power X c.
```

Here `power` is represented variable-base model exponentiation and the
repository's `ycoord` uses the paired-Pell parameter. In the ordinary note's
indices, `n=m+3c+1` and `r=s+1`; thus the hypothesis is `r≤n+c` and the
conclusion is the subtraction-free version of
`Y^(n−c)<2^(2c−1)X^c`. The auxiliary power-gap theorem assumes the
corresponding strict represented-power gap instead of the Pell gap.

The proof uses existing model power-addition and multiplication-of-bases
laws, monotonicity and positive cancellation. It does not derive the Pell
gap or index window from a graph zero, cover the boundary `n=3c`, prove
the variable-width lower-power estimate or reverse guard, or establish an
iPRA endpoint.

The author check used:

```text
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-variable-width-pell-height \
  Computability/DiophantineConsistency/research/trace74-variable-width-pell-height/Trace74VariableWidthPellHeight.lean \
  -o /tmp/Trace74VariableWidthPellHeight.olean
```

Actual session 60717 exited 0 with no warnings; both reports list only
`propext`, `Classical.choice`, and `Quot.sound`. An earlier run exited 1
because an extra `rfl` followed a solved goal; that run is not a proof.
SHA-256: source
`1ad8a189f1a7bd78e79f59608f0e4c7eb7d2ed0fa05a4b287c07347ff974f364`,
output object
`3957186ad270213a2ae188e718eb91d2aac7895035063aed8ac6ab0b135cb6e4`,
imported `Trace74NearDiagonalPellModel.olean`
`af9a5f302648ea6bab75b3bb62c8ba74e48c3922f68b0af30364b22991d621bb`,
Lean executable
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Temporary providers and transitive/package/dynamic/search-path ancestry are
not independently authenticated; this is not a clean current-source build
or independent replay.
