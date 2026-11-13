# Linked-index separation for a fixed-symbolic trace74 zero

`Trace74NearDiagonalFixedClient.graph_main_separated` uses the same-zero near-diagonal exclusion to show `n+2 < r` for supplied first and main ordinate indices with `r ≥ 11`, `q ≥ 2³⁰`, and a positive actual trace74 graph zero. Its case `n < 8` is excluded directly from `r ≥ 11`; otherwise the near-diagonal theorem applies.

`fixed_exists_separated_indices` supplies one linked pair for a positive trace74 zero whose first port is `CompactFixedBeta.betaNat`: `n ≥ 7`, `r ≥ 11`, `n+2 < r < 2n`, odd `r`, both actual ordinate identities, and the first-index residue modulo `q⁴`. The remaining three ports are arbitrary. This does not prove index equality, a reverse guard, absence of zeros, 74/75 equivalence, or an iPRA endpoint. The external fixed payload's connection to the symbolic ports is outside this check.

An author check used Lean 4.32.0, `-M3000 -j1 -DElab.async=false`, a 120-second subprocess timeout, and this directory as `--root`. `LEAN_PATH` was `/tmp:` prepended to the captured `lean_path` field from [`trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json). The output object was `/tmp/Trace74NearDiagonalFixedClient.olean`. The final subprocess exited 0 without warnings, and both theorem axiom reports were `[propext, Classical.choice, Quot.sound]`. One earlier attempt failed on an addition-order mismatch and is not a successful proof.

```text
Trace74NearDiagonalFixedClient.lean  97d2f9d1985b44f0622a4e84516ca11f6958adabd3258b17555275478f04447d
Trace74NearDiagonalFixedClient.olean 9307af5c52d317b5e4079072cc1c9182789d8fe796403a445a6caf4662e39557
Trace74NearDiagonalGraphJoin.olean  64856c47d738c01ef643eff2c90f48efb52f2372d1e8fbbeef688764c9a3a177
Trace74FixedMainIndexEleven.olean   394c4f1aebbd646d776a20832fd04a01ec817a3e0a49dd8c00e39f56ef3d5d70
```

This is an author check against temporary captured providers, not an independent replay. Their full transitive/package/dynamic ancestry and the combined search-path selection were not independently authenticated in this check.
