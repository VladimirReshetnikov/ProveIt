# Strong Pell chart binding in every commutative ring

`Trace74StrongChartBinding.strong_outputs` proves the polynomial identities
behind the strong chart: if `U*tau=y`, `phi²=1+delta*y²`,
`f=2phi²−1`, and `I=2delta*phi*y`, then the strong square, trace
coefficient, and auxiliary-Q expressions are respectively `phi²`, `f`,
and `I²`. The result requires only a commutative ring.

`graph_strong_outputs` binds these identities to the **actual** 74 graph
chart and component definitions, with explicit same-tuple identities for
`c`, `E=tau²`, the discriminant and scaled ordinate. It derives the actual
chart `F=phi²`, component `f=f`, and chart `Q=I²`. It does not construct a
Pell seed, derive those hypotheses for the fixed candidate, or establish a
graph zero, reverse guard, or iPRA endpoint.

Lean 4.32.0 session 67936 exited 0 with no warnings. Both printed axiom
reports list only `[propext, Quot.sound]`. The previous run failed during
elaboration of an over-expanded chart expression and was rejected. The
successful run used:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=research/trace74-positive-carrier \
  research/trace74-positive-carrier/Trace74StrongChartBinding.lean \
  -o /tmp/Trace74StrongChartBinding.olean
```

Source SHA-256:
`9ff59c6581a7a0f7a47a30a22aa84e033e9e4b5d7a340779bc73bb5d5694e5d2`.
Output object SHA-256:
`3b877fb1c74d3bd904b2a903a0e2b6dae7a7523f38541c997079eae891c19e7d`.
Imported `Trace74DynamicRegisters.olean` SHA-256:
`7ac639b7f868106fb0d9fd30ae0f816817c237c52eb21eaeb01bed1a967f8743`.
The temporary captured provider, transitive/package/dynamic ancestry and
search-path resolution are not independently authenticated. This is not a
clean current-source rebuild or independent replay.
