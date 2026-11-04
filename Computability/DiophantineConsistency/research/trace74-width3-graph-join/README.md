# Width-three index exclusion for a trace74 graph zero

`Trace74Width3GraphJoin.graph_width3_large_q_impossible` proves in Lean,
for every model of `IΣ₁`, that a single positive 74-operation graph zero
cannot have supplied first and main Pell ordinate indices `n,r` satisfying
`n≥12`, `r≤n+3`, and `q≥2³⁰`. The first port is positive; the other ports
are arbitrary. Both ordinate equations refer to that same graph valuation.

The proof joins the width-three Pell height bound, the cubic-size lower
power bound, height amplification, and the same-zero projection
contradiction. The companion theorem `graph_width3_impossible` leaves the
lower power inequality as an explicit premise. The final theorem derives
it from `q≥2³⁰`, `Y=q³v₆`, and `b<q`, using `d=n−12`.

This is an exclusion of the stated index window, not a proof of the
reverse guard, general absence of zeros, 74/75 equivalence, or an iPRA
endpoint. It does not exclude first indices `n<12` or wider gaps. The
fixed-symbolic tuple's link to the external payload remains outside this
check.

The Lean 4.32.0 author check used `/tmp:` prepended to the captured
`lean_path` field from
[`trace74-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-main-index-eleven-draft/observations/attempt01/terminal.json),
`timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and output `/tmp/Trace74Width3GraphJoin.olean`. Actual tool
session 91580 exited 0 without warnings; both reports list only `propext`,
`Classical.choice`, and `Quot.sound`.

```text
Trace74Width3GraphJoin.lean         528de8ddfdba7addad32496d6e524656609777cdde1ad4bc8dca6e33208e7f2c
Trace74Width3GraphJoin.olean        39cc9dfd8470348527a0354cb4ec5c6f741347e4914e5753506a3d135618e1a0
Trace74Width3PellHeightModel.olean  cd165fc9aa8dc39d2bc44f1b6a9c096c197c9065fe22b2d02b586ccda99c4110
Trace74Width3AmplificationModel.olean 3b801f28a7924d648ba62938b4ade910b2c03cbdfbe1744bb4722bf4b5adb1be
Trace74Width3SizeModel.olean        c5c19b202e4f444d9af79a3d22a50e1a195900285c96a9ecb0a810d71e9b3049
Trace74UniformGraphHeight.olean     6dda6fe14df3240b8bca062ef1a44a82d7060c44fb8eab742aac329b18e8e582
Trace74PellGapBinding.olean         8ffc0282fa2dc540cbba08255c19ca780234da569fd2ad2b1163418c0966445a
```

This is an author check using temporary captured providers, not an
independent replay or coherent current-source rebuild. The complete
transitive/package/dynamic ancestry and search-path selection were not
independently authenticated.
