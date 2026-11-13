# Near-diagonal index exclusion for one trace74 zero

`Trace74NearDiagonalGraphJoin.graph_near_diagonal_large_q_impossible` proves in Lean, in every model of `IΣ₁`, that the following cannot all hold for **one** positive witness tuple and its 74-operation graph valuation:

* the graph is zero, its first port is positive, and `q ≥ 2³⁰`;
* the supplied first and main Pell ordinate equations both hold for that tuple at internal indices `n` and `r`;
* `n ≥ 8` and `r ≤ n+2`.

The proof derives `n < r` from those same-tuple ordinate equations, obtains the strict Pell gap and near-diagonal power upper bound, proves the necessary lower power bound using `q ≥ 2³⁰` and the graph quantities' definitions, amplifies the two bounds into a height inequality, and combines it with the same-zero graph projection. The companion theorem `graph_near_diagonal_impossible` makes the lower power inequality an explicit premise; the large-`q` theorem discharges it.

This excludes only the near-diagonal window. It does not prove a reverse guard, equality of indices, general absence of zeros, 74/75 equivalence, or an iPRA endpoint. The link between fixed symbolic ports and the external displayed payload remains outside this check.

The author invoked Lean 4.32.0 with `-M3000 -j1 -DElab.async=false`, a 120-second subprocess timeout, and this directory as `--root`. `LEAN_PATH` consisted of `/tmp:` followed by the captured `lean_path` field from [`trace74-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-main-index-eleven-draft/observations/attempt01/terminal.json). The output object was `/tmp/Trace74NearDiagonalGraphJoin.olean`. The final subprocess exited 0, without warnings; both theorem reports list only `[propext, Classical.choice, Quot.sound]`.

```text
Trace74NearDiagonalGraphJoin.lean       b731550ee81fea3a74f762d0a17dab594d73df2f8e1f3769ef0cb0704f4646d0
Trace74NearDiagonalGraphJoin.olean      64856c47d738c01ef643eff2c90f48efb52f2372d1e8fbbeef688764c9a3a177
Trace74PellGapBinding.olean            8ffc0282fa2dc540cbba08255c19ca780234da569fd2ad2b1163418c0966445a
Trace74NearDiagonalLargeHeightModel.olean 01b02431bd9afe6f85c07190976b120c27519310807e2936a0282ba5a7b96252
Trace74UniformGraphHeight.olean        6dda6fe14df3240b8bca062ef1a44a82d7060c44fb8eab742aac329b18e8e582
Trace74NearDiagonalSizeModel.olean      dd4398cd1513c2e05fdca415c8fa76a75c4d40862fe2d7a5db3047df054f1513
```

This is an author check using temporary captured provider objects, not an independent replay or coherent current-source rebuild. Full transitive/package/dynamic ancestry and search-path selection were not independently authenticated here.
