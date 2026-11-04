# Main-ordinate residue for the positive offset

`Trace74MainOrdinateOffsetResidue.tuple_offset_residue` proves in each
`IΣ₁` model, for any tuple with `Y>0` and a supplied main Pell ordinate
`c=ycoord r (A−1)`, that

```text
v₈ mod Y = r mod Y.
```

It applies the represented Pell residue theorem modulo `Y`, using
`A=Y(X+1)` and `c=kY+v₈`. The companion theorem retains the actual
positive split `k=v₈+v₉` and supplies `0<v₈<k`. These are conditional
same-tuple facts; no graph zero or bound on the size of the residue is
assumed or inferred. They do not by themselves settle the reverse guard,
the actual fixed payload binding, or an iPRA endpoint.

A Lean 4.32.0 author check used `-M3000 -j1 -DElab.async=false`, a
120-second subprocess timeout, and this directory as `--root`. Its
`LEAN_PATH` was `/tmp:` prepended to the `lean_path` field in
[`trace74-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-main-index-eleven-draft/observations/attempt01/terminal.json).
The output was `/tmp/Trace74MainOrdinateOffsetResidue.olean`. Tool
session 77381 exited 0; both reports list only `propext`,
`Classical.choice`, and `Quot.sound`. An earlier check failed on a
positivity elaboration and is not accepted.

Source SHA-256:
`5a57c287ff258c23f4c5b03a6ac55a413459befdcc1cc782beaa6c1d1e2fd9d4`.
Output object SHA-256:
`42d992613f5927202e032b8a5f5a24a200b0b028cb74c4fb6e2e6cb7571e3cb2`.
Direct imported `Trace74PellGapBinding.olean` SHA-256:
`8ffc0282fa2dc540cbba08255c19ca780234da569fd2ad2b1163418c0966445a`.
This captured-provider author check does not authenticate transitive,
package or dynamic ancestry or search-path selection, and is not a clean
current-source rebuild or independent replay.
