# Compact44 word-cell contribution to cyclic product columns

`CompactWordProductColumn.lean` gives a conditional all-model bridge from
the checked word-cell aggregate to the two actual symbolic-kernel cyclic
product digits. For a compact word cell `j`, it proves that reflected source
offsets read positions `8807*j+e` without wrapping whenever the target lies
inside the packed word. Under the explicitly stated selector and payload-bit
identities for a proposed packed word `C`, the corresponding selected band
contributes exactly `1 + 2^51` at either target phase.

For each phase, the final theorems give an exact formula for the digit of
`((paramKernel rho)*C + T) mod (2^(67*n)-1)`. They require a
`CarryInput` for **that exact output**, the actual two-band coefficient and
rotated-word family, explicit packed selector/copy source-digit identities,
the model word bounds, and the target index bound. They retain every other
contribution: the opposite reflected band, the five bare rotations, the
temporal-word digit, and the incoming end-around carry. The result is taken
modulo `2^67` as dictated by the carry equation. No contribution is assumed
zero and no incoming carry is silently dropped.

This connects the selected word-cell aggregate to the symbolic cyclic product
**conditional on those hypotheses**. It does not construct `C`, prove the
packed-digit identities or the `CarryInput`, identify `T` with the required
temporal multiplication, bound or clear the other contributions, prove that
the complete product equals the previously constructed sparse target block,
establish graph zero, bind retained bytes, or produce an iPRA derivation.

## Observed checks

The first bounded attempt, session `3333`, exited 1: the selected-band theorem
checked, but the first product-column theorem failed to rewrite a cast
numeral. Its exact source and log are retained under `observations/`; the
failed final theorem printed `sorryAx` through error recovery and is not
accepted. The final source, identical to attempt 02, also includes the second
target. Session `4604` actually exited 0 with four named axiom reports, no
warnings and no `sorryAx`; each report lists only `propext`, `Classical.choice`
and `Quot.sound`. Lean used `-M3000 -j1 -DElab.async=false`, a 120-second
timeout and
`LEAN_PATH=/tmp/ipra-compact-word-cell-author-01/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`;
no output object was requested.

The checked source SHA-256 is
`9488c92a75e20962dc82fa8f84fe3aae84cfd68d1f3a00598651a28e5ac890ca`;
its final log SHA-256 is
`feb34021cd19fd5f3eb6d0a6162480b09e0f50ee13a854a90882a157bc8b342e`.
Post-run direct object snapshots are `CompactWordCellClient.olean`
`56ced49c140437f4080d25499828285386e881389e6ea6a418e18dab3d46bed8`
and `RawColumnBands.olean`
`c460dbc08c04564325d791f417adeee385072696017d7539ac634a42b68991a5`.
These snapshots do not authenticate dependency resolution during the run.
This is a single-author incremental observation, not a paired replay,
independent Lean reconstruction or full project/package/dynamic ancestry audit.
