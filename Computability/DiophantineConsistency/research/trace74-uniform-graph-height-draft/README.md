# Conditional same-zero projection height contradiction

`Trace74UniformGraphHeight.graph_height_impossible` proves in Lean, for any model of `IΣ₁`, that the following cannot all hold for **one** tuple: a positive first port and positive witnesses; a zero of the 74-operation graph; a main Pell ordinate at an internal index `r ≥ 2`; and the explicitly assumed height inequality

```text
8 b (2^r)^2 Y^2 < X.
```

Here `2^r` is the model's represented exponential `Exp.exp r`, with `b`, `X`, and `Y` the trace74 quantities. The proof instantiates the same-zero reduced projection and the ordered-ring size contradiction in the model's difference ring. It derives the ring's discreteness, positivity, and `2^r = 4·2^(r−2)` from the supplied model assumptions. All quantities refer to the same graph valuation and ordinate index. The corollary `graph_height_upper` removes the height premise and gives the complementary bound `X ≤ 8 b (2^r)^2 Y^2` for every such zero and ordinate index.

The strict height inequality is a **premise** of `graph_height_impossible`; neither theorem derives it from the Pell gap or an index window, excludes an index range without further hypotheses, proves a reverse guard, or establishes an iPRA endpoint. In particular, no near-diagonal bound has been established here.

The author invoked Lean 4.32.0 with `-M3000 -j1 -DElab.async=false`, a 120-second subprocess timeout, and this directory as `--root`. `LEAN_PATH` consisted of `/tmp:` followed by the captured `lean_path` field from [`trace74-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-main-index-eleven-draft/observations/attempt01/terminal.json). The output object was `/tmp/Trace74UniformGraphHeight.olean`. The final subprocess exited 0 and both axiom reports were `[propext, Classical.choice, Quot.sound]`.

```text
Trace74UniformGraphHeight.lean         b804e669009921a591a20f2b52b6d4a474c3d0ec28f54dc414f4ef23a10e5597
Trace74UniformGraphHeight.olean        6dda6fe14df3240b8bca062ef1a44a82d7060c44fb8eab742aac329b18e8e582
Trace74UniformProjectionGraph.olean    e7e72f7339c7f5c2d876b82c0ac4ed84aac32a0c9a01b80291e52904eb4cc92c
Trace74UniformHeightContradiction.olean c994954d496b9bc17f1354d28342699e2b0e02bd91eac3f0c3333421143c159e
```

This is an author check against captured temporary provider objects, not an independent replay. Their complete transitive/package/dynamic ancestry and search-path selection were not independently authenticated in this check.
