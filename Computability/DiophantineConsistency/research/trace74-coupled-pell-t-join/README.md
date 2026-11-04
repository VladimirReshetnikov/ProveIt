# Positive trace coordinate from one coupled Pell quotient

`Trace74CoupledPellTJoin.positive_T_from_coupled_pell` works in every
`IΣ₁` model. For one set of internal `a,t,j,s,I,c,N`, it joins the exact
two-modulus auxiliary Pell residues with the positive-coordinate theorem.
Write

```text
f=xcoord (2t) a,
Q=oddQuotient (2(j+t(2s+1))) (I−2).
```

Under explicit premises `I≥2`, `c>0`, the strong norm
`I²+delta(a)=delta(a) f²`, `c|I`, `c|t`, `c=ycoord (4j+1) a`,
`N mod c=(4j+1) mod c`, `f mod c=1 mod c`, and
`f(N+c)≤Q+c`, the theorem constructs `T>0` with
`Q+c=f(cT+N)`. In the proposed negative-rank construction `N` is the
magnitude of the signed rank.

The norm, divisibilities, residue and size bound remain explicit; no
choice of auxiliary index or graph zero is constructed here. This is not
a full counterexample certificate or iPRA endpoint.

The Lean 4.32.0 author check used `LEAN_PATH=/tmp:` followed by
`/tmp/trace74-direct-four-block-1zltaw2f/lib` and
`/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`, `timeout 120`,
`-M3000 -j1 -DElab.async=false`, this directory as `--root`, and output
`/tmp/Trace74CoupledPellTJoin.olean`. Actual session 41471 exited 0
without warnings and reported only `propext`, `Classical.choice`, and
`Quot.sound`.

Source SHA-256:
`f25f7c816f33e8502fd43eb387d884b2328b70966c379821780ce86ce8b54248`.
Output object SHA-256:
`45ee424ee6f5baf1bcef8d75ed7e8ded07b5acebfcc73d6cb4b7c60e9df8899b`.
Direct imported `Trace74CoupledPositiveT.olean` SHA-256:
`565f77a92282333715a11d08fbe9acec3dcc24a2cfdcb0e0252cf0f58be36038`.
The captured providers and full transitive/package/dynamic ancestry and
search-path resolution have not been independently authenticated. This
is not a coherent current-source rebuild or an independent replay.
