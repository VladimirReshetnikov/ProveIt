# Root review of the resumed Carrier65 arithmetic checkpoint

Result: PASS for the four local arithmetic modules and their focused checks.
The final consistency-equivalence goal remains open.

ROOT read every line of `Carrier65`, `FirstPellCarrier`, their focused
checks, and the invoked sign formulas, comparing the literal front with
the maintained decimal2011 TeX. ROOT authored and read `CarrierRankBounds`,
`Carrier65Witness` and their checks. Independent reviews of the actual front
and the rank/witness integration are saved beside this receipt; authorship
of a dependency is distinguished from independent review.

The polynomial has exactly the displayed fourteen coordinate slots and
four ordered ports. The source mask is already shifted once. Its
evaluation identity holds on all integer assignments. On positive zeros,
the proof cancels the positive discriminant and excludes the four negative
norm units before drawing any conclusion about the carrier or rank. This
forces the transport factor to one. That unit forces C positive, and the
literal rank satisfies `q*(q^2-1)<R<q^4-q^3`. Positive w,s give `1<R` and
`R+2<E`. These are consequences, not extra premises in the integrated
polynomial theorem.

The first-Pell classification gives the congruence and gap after the least
positive solution. They prove that the restored integer quotient is
strictly positive and unique. The converse map gives a positive new carrier
from the canonical positive first-root/index interface. The rank-one
counterexample in the focused checks explains why the strict lower bound
cannot be omitted. No native interpretation or consistency premise is
used in any of these new theorems.

ROOT freshly ran the following successfully from this worktree:

```text
lake env lean Computability/DiophantineConsistency/Lean/DiophantineConsistency/Carrier65.lean -o .lake/build/lib/lean/DiophantineConsistency/Carrier65.olean
lake env lean Computability/DiophantineConsistency/Lean/DiophantineConsistency/Carrier65Checks.lean
lake env lean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CarrierRankBounds.lean -o .lake/build/lib/lean/DiophantineConsistency/CarrierRankBounds.olean
lake env lean Computability/DiophantineConsistency/Lean/checks/CarrierRankBounds.lean
lake env lean Computability/DiophantineConsistency/Lean/DiophantineConsistency/FirstPellCarrier.lean -o .lake/build/lib/lean/DiophantineConsistency/FirstPellCarrier.olean
lake env lean Computability/DiophantineConsistency/Lean/DiophantineConsistency/FirstPellCarrierChecks.lean
lake env lean Computability/DiophantineConsistency/Lean/DiophantineConsistency/Carrier65Witness.lean -o .lake/build/lib/lean/DiophantineConsistency/Carrier65Witness.olean
lake env lean Computability/DiophantineConsistency/Lean/checks/Carrier65Witness.lean
```

The printed theorem-axiom reports contain only `propext`,
`Classical.choice` and `Quot.sound`. No `sorry`, new axiom, native-decide
trust extension or target-equivalence assumption was introduced.

The environment is Lean4.32.0, with the repository-pinned mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`. The existing dependency cache
was used after exact source-byte comparison for all34 custom prerequisite
modules against the prior worktree. The durable
`carrier65-lean-dependency-cache.json` records their source/object hashes.
`ConsecutivePell` was also freshly lake-built. The attempted serial full
prerequisite rebuild was deliberately stopped after its first completed
module to reuse the authenticated cache; no full ancestral replay is
claimed. The complete281-module umbrella was not rebuilt in this checkpoint.

The full fixed-port formula and its inequalities, current942-tile machine
calibration, global soundness and canonical completeness, recent13-variable
maps, other frontier equations and internal object-ZFC derivation remain
required by the active plan. Operation-count and exact-degree claims here
retain their earlier finite/ordinary evidence; these new Lean modules
prove arithmetic, rather than those metrics. The main TeX/PDF and frozen
ordinary packets retain their existing bytes.
