# Generic whole-field cycle exclusions: author receipt

This records a complete author self-review and fresh Lean replay, not an
independent peer review. The frozen sources are:

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
| --- | --- |
| `NativeFieldCycles2011.lean` (111 lines) | `9cac50de2b83d3b802eab615ab4340027b842abc910586d009c4847b913f8442` |
| `NativeFieldCycles2011Checks.lean` (64 lines) | `3682208abe906dade29dd135861743ec0e955e1a324a1841611cb1bf59e077ac` |

The only main imports are `Mathlib.Dynamics.PeriodicPts.Lemmas` and
`Mathlib.Tactic`. The module has no project dependency and no native word,
mask, coefficient, tile, label, machine or consistency premise.

`offset19_excludes_510` has exactly the planned hypotheses: a finite type,
a permutation sigma, natural values S<512 and epsilon≤1, recurrence
`S(sigma i)=(2*S i+epsilon i)%512`, and one fixed exceptional source value
sstar with `epsilon i=1 → S i=sstar`. It concludes that S never equals510.
Three predecessors of510 force two consecutive exceptional bits, so
sstar=511. Every forward iterate from510 is then even. At an even source
the exceptional bit is zero, so every successor has residue0 modulo4.
A positive return period, obtained from the finite permutation, contradicts
510's residue2 modulo4. This replaces the proposed explicit eight-step
orbit with a smaller periodicity argument; the mathematical hypotheses
and conclusion are unchanged.

`offset20_excludes_510` needs only an arbitrary type, an arbitrary source
function theta, natural values S and e≤2, and
`S i=(4*S(theta i))%512+e i`. Two consecutive recurrence instances give
the contradiction modulo4. No finite type, permutation, bound on S or
terminal-color condition is assumed.

The focused checks construct the genuine511 self-loop with epsilon=1,
sstar=511 and nonzero S, satisfying every offset19 hypothesis. They also
construct a zero cycle where the exceptional branch is never used, apply
offset20 on the infinite type Nat with arbitrary theta, and discharge its
e≤2 premise from two mutually exclusive Boolean selector indicators.
No theorem claims all cycles are zero.

After reading the complete final main/check sources, both fresh commands
exited0 from the repository root with asynchronous elaboration disabled:

```sh
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/NativeFieldCycles2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeFieldCycles2011.lean
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/NativeFieldCycles2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeFieldCycles2011Checks.lean
```

The final main log `/tmp/native-field-cycles-stage3.log` is empty. The
checks log `/tmp/native-field-cycles-checks-stage1.log` reports only
`propext`, `Classical.choice`, `Quot.sound` for offset19 and only `propext`,
`Quot.sound` for offset20. Neither source contains `sorry`, `admit`, a new
`axiom`, or `native_decide`.

These are generic arithmetic lemmas. The actual copy-mask equalities,
South-bit reconstruction, source-cell translation, terminal-selector
calibration and coarse offset split must still be bound to them before
they establish the current equation's whole-field alignment. Existing
frozen sources were not edited and no commit was made by this author.
