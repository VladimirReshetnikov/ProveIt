# Same-zero variable-width Pell index obstruction

`Trace74VariableWidthGraphJoin.graph_variable_width_impossible` proves a
conditional same-zero obstruction in every model of `IΣ₁`. It rules out
one positive trace74 zero with positive first port and **the supplied same
tuple's** first/main ordinate equations at indices

```text
n = m+3w+1,   r ≤ n+w,
```

when the following explicit model hypotheses also hold:

```text
power 2 B ≤ q,
e+w = 3(m+1),
2w(n+w)+5w ≤ B e.
```

All `m,w,r,B,e` are arbitrary internal model elements. The proof derives
the strict Pell gap from the positive tuple, applies the variable-width
Pell-height and size lemmas, and contradicts the same-zero projection
height bound. It establishes that the main index is at least two rather
than assuming its parity. Other than the first port, ports are arbitrary
natural numbers.

`fixed_graph_variable_width_impossible` specializes the same result to
`p 0=CompactFixedBeta.betaNat`, using the checked symbolic lower bound
`power 2 ((67:V)*8807)≤q`. It retains the ordinate, window, auxiliary
equation and threshold hypotheses; no huge power of two is evaluated.

These are **model-level conditional exclusions**. They do not show that
the threshold holds for arbitrary indices or that every possible gap is
excluded; `n=3w` is outside this parameterization. The external payload
link, reverse guard, 74/75 equivalence, complete source provenance and iPRA
endpoint remain open.

An author check used Lean 4.32.0 with `timeout 120`, `-M3000 -j1
-DElab.async=false`, this directory as `--root`, and output
`/tmp/Trace74VariableWidthGraphJoin.olean`. `LEAN_PATH` was `/tmp:`
prepended to the captured `lean_path` field in
[`trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json).
Actual tool session 32066 exited 0 with no warnings; both reports listed
only `propext`, `Classical.choice`, and `Quot.sound`.

```text
Trace74VariableWidthGraphJoin.lean   f04f03c02b7e3e5cd3a468013169ea2583abcf3e0405b022657b3a2e5dd0335e
Trace74VariableWidthGraphJoin.olean  57b72440c2dc905ce2a3ef1026a942c440a1709e2915955341e494a34e8c47e4
Trace74VariableWidthAmplification.olean b2eb228fa7811228d64993dacf68a3703d703b555d14677fb3da934f24747a52
Trace74FixedQSymbolicBound.olean     b4b0963e952ec4c290c69d1d1a3edb7b35cd59848c34946457f15c135a57de2d
Trace74PellGapBinding.olean          8ffc0282fa2dc540cbba08255c19ca780234da569fd2ad2b1163418c0966445a
Trace74UniformGraphHeight.olean      6dda6fe14df3240b8bca062ef1a44a82d7060c44fb8eab742aac329b18e8e582
```

This is an author check against temporary captured providers, not an
independent replay or coherent current-source rebuild. The complete
transitive/package/dynamic ancestry and search-path selection were not
independently authenticated here.
