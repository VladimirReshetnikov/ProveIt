# Width-three height amplification in arithmetic models

`Trace74Width3AmplificationModel.amplified_height` proves in any model of
`IΣ₁` that `8hK²Y² < X` follows from `Y≥1` and the two explicitly supplied
represented-power inequalities

```text
power Y (k+6) < 32X³,    16384h³K⁶ < power Y k.
```

The proof expands the fixed sixth power, multiplies the lower inequality by
`Y⁶`, cancels 32, and compares cubes. The corresponding graph application
would use `k=n−9`. This lemma does not derive either power bound, the index
window, or a graph contradiction; it is not an iPRA endpoint.

A captured-provider author check used the following command:

```text
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-width3-amplification-model \
  Computability/DiophantineConsistency/research/trace74-width3-amplification-model/Trace74Width3AmplificationModel.lean \
  -o /tmp/Trace74Width3AmplificationModel.olean
```

Tool session 58491 exited 0 and its theorem report listed only `propext`,
`Classical.choice`, and `Quot.sound`. Source SHA-256 is
`5a4ff0a6f1e920fe2fcd25a7e73ffcaa615f8d0012bd9792732471123b593bb9`, object
SHA-256 is `3b801f28a7924d648ba62938b4ade910b2c03cbdfbe1744bb4722bf4b5adb1be`,
and the direct imported `Trace74NearDiagonalLargeHeightModel.olean` SHA-256
is `01b02431bd9afe6f85c07190976b120c27519310807e2936a0282ba5a7b96252`.
The temporary captured providers and their transitive/package ancestry and
search-path resolution were not independently authenticated; this is not a
clean current-source build or independent replay.
