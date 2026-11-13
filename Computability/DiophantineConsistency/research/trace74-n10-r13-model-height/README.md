# Same-tuple height for indices 10 and 13

`Trace74N10R13ModelHeight.tuple_height` proves, in every model of `IΣ₁`,
that a positive first port and witness tuple with `q≥2³⁰`, whose first and
main Pell ordinates have indices 10 and 13 for that same tuple, satisfy
`536870912 b Y < X`. The conclusion is in the model's difference ring.
It combines the same-tuple Pell gap, the width-three model height estimate,
and the ordered-ring growth lemma. It does not require a graph zero.

The theorem does not bind this bound to a graph projection, exclude a
graph zero, establish a reverse guard, or prove an iPRA endpoint.

The Lean 4.32.0 author check used `/tmp:` prepended to the captured
`lean_path` field from
[`trace74-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-main-index-eleven-draft/observations/attempt01/terminal.json),
`timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and output `/tmp/Trace74N10R13ModelHeight.olean`. Actual tool
session 91208 exited 0 without warnings; the report lists only `propext`,
`Classical.choice`, and `Quot.sound`.

```text
Trace74N10R13ModelHeight.lean       fdb90c18c6e1358147eb57ad13daa2c3c23f2bb2d918c890f1fd1d7d8e56cc04
Trace74N10R13ModelHeight.olean      7a34eef8ce70dc67a2eb7d49772d53aaa100dcb51def96ba7daa5aea7d95f0c4
Trace74R13Height.olean              a46433cc3b822986c80d12f248861d3a9ff1a71580db9e179f6b816720a4231e
Trace74Width3PellHeightModel.olean  cd165fc9aa8dc39d2bc44f1b6a9c096c197c9065fe22b2d02b586ccda99c4110
Trace74PellGapBinding.olean         8ffc0282fa2dc540cbba08255c19ca780234da569fd2ad2b1163418c0966445a
```

This captured-provider author check is not an independent replay or a
coherent current-source rebuild. Full transitive/package ancestry and
search-path selection remain unauthenticated.
