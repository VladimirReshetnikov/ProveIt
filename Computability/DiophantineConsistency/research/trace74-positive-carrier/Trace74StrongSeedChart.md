# Constructing and binding the strong seed to one 74-chart tuple

`Trace74StrongSeedChart.exists_strong_chart` proves in every model of
`IΣ₁` that a single positive Pell seed `t,i` can be chosen, with `c|t`
and `y_t=(c²*tau)*i`, so that after updating coordinate 3 of one base
tuple the **actual 74 chart** has `F=phi²`, `Q=I²`, and the trace
coefficient `f=x_(2t)`. It also retains the seed's strong norm, `c|I`,
`I≥2` and `f≡1 mod c`. All outputs concern that same updated tuple.

The theorem assumes positive `c,tau` and three explicit base identities:
the chart's main `c`, the first square `E=tau²`, and its discriminant
equal the stated model values. The model tuple's other required base values,
positivity, carrier offset, fixed-port CRT and actual first square remain
unproved in this module. It does **not** assert a graph zero, a reverse
guard or an iPRA endpoint.

The author check invoked Lean 4.32.0 as follows:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=research/trace74-positive-carrier \
  research/trace74-positive-carrier/Trace74StrongSeedChart.lean \
  -o /tmp/Trace74StrongSeedChart.olean
```

Actual tool session 88365 exited 0 with no warnings; its axiom report lists
only `[propext, Classical.choice, Quot.sound]`. The previous run failed on
missing Pell-periodicity namespace imports and was not accepted.

```text
Trace74StrongSeedChart.lean              09535dff7ffb447649e6657e1074d092565d8da2360aba2fb9292a6329d45c11
Trace74StrongSeedChart.olean             1302e8a76b336cb06616bfc2813a833b5296a85749bc524f6dc20d35addf5b9a
Trace74StrongChartBinding.olean          3b877fb1c74d3bd904b2a903a0e2b6dae7a7523f38541c997079eae891c19e7d
Trace74CoupledPellStrongSeed.olean       64ddb5b1ed1be97e7bc7160b5c811cd638529ce10c2cc377aec08dcc7c1a1329
```

This is an author check with temporary captured providers; transitive,
package, dynamic and search-path ancestry are not independently
authenticated. It is not a clean current-source build or independent replay.
