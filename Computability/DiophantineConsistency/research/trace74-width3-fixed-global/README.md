# Global width-three separation at symbolic beta

`Trace74Width3FixedGlobal.fixed_exists_width3_global` proves in Lean, in
every model of `IΣ₁`, that one positive trace74 graph zero whose first port
is the fixed symbolic `betaNat` has linked first and main Pell indices
`n,r` with `n≥7`, odd `r≥11`, and **`n+3<r<2n`**. Both ordinate identities
and the first-index residue modulo `q⁴` are retained for that same pair;
the remaining three ports are arbitrary.

The proof uses the width-three graph exclusion for `n≥12`. For smaller
`n`, it eliminates main index 11 at first indices at least 8, eliminates
the pair `(10,13)`, and uses oddness of the main index for the remaining
even numerals. It derives a separation bound, not a reverse guard, absence
of zeros, 74/75 equivalence, or iPRA endpoint. The binding of the symbolic
ports to the external fixed payload remains outside this check.

The bounded Lean 4.32.0 author check used `/tmp:` prepended to the
`lean_path` field in
[`trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json`](../trace74-fixed-main-index-eleven-draft/observations/attempt01/terminal.json),
with `timeout 120`, `-M3000 -j1 -DElab.async=false`, this directory as
`--root`, and output `/tmp/Trace74Width3FixedGlobal.olean`. Actual session
28888 exited 0 without warnings; the axiom report lists only `propext`,
`Classical.choice`, and `Quot.sound`. The first author check failed on
elementary parity and addition-normalization goals, which were corrected.

```text
Trace74Width3FixedGlobal.lean        424aa1047144a05285b1408b3d32918297614d13c83fdde8c08c9869559a7679
Trace74Width3FixedGlobal.olean       67534a0145c69b65b35727987bd91fdf85b515e9ea24215aa602216d29a83e96
Trace74Width3FixedClient.olean       d2950932241da27e1271aba8f1f59e490241fff400cb6a7500709ee71afaec70
Trace74AtLeastEightR11GraphExclusion.olean 022aafacecd9158d650b08562ffa893aa457bc9f430cbc102eb4c174e2b7a9e1
Trace74N10R13GraphExclusion.olean    a16bc0ffcf0b8905d8caa01af667a3e77a9a93bcf9aabc041072b75bc98a787c
```

This captured-provider author check is not an independent replay or a
coherent current-source rebuild. Full transitive/package ancestry and
search-path selection have not been authenticated.
