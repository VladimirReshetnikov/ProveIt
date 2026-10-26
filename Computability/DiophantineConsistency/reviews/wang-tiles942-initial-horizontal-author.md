# Author receipt: exact horizontal initialization colors

Date: 2026-10-26 UTC. Author: `controller_certificate`, at root's assignment.
Status: frozen, complete source/check self-read and fresh bounded Lean
compilation PASS. This is an author receipt, not an independent review.
The packet is confined to the actual finite `Allowed` tile language.

All source paths are relative to `Lean/DiophantineConsistency/`.

| File | Lines | SHA256 |
| --- | --- | --- |
| `WangTiles942InitialHorizontal.lean` | 136 | `f989a80b56aac3c1ee31f41fc18cd4e4ac0486bbce73cb22d220f6630ced9536` |
| `WangTiles942InitialHorizontalChecks.lean` | 70 | `97bca6abaa994b64a9d41e246c90dc9d9e4dab747ab51353737a75c03e0b813c` |
| Imported `WangTiles942Language.lean` | — | `a28056b4929cfea69255619b5d89b5f7a64dc47efe0e94ca2e43e00f7788228d` |

I read the complete existing Language and Boundary sources, including all
ten `Allowed` constructors and the direction-restricted rail bounds, before
implementation. Boundary was inspected for consistency of API and color
conventions but is not imported by the new main. Both complete new sources
were read before execution, and the two later linter-only line changes were
read before the final replay.

`small_horizontal_cases` first classifies any allowed tile with a horizontal
edge in2..4. Transition and receiving tiles have each horizontal edge either
zero or a valid rail. Actual action-target membership and the actual
direction-specific target condition give rail≥6, so neither family enters
that range. Pass and finish edges are0; reset edges are1. The only remaining
families are Start, the three initializers, and seams.

The five exported equivalences, under the single local premise `Allowed t`,
are exactly:

| Edge condition | Exact tile possibilities, in West/North/East/South order |
| --- | --- |
| `t.east=2` | `(2,434,2,0)` or `(a²,437,2,437)`, `a : Fin 3` |
| `t.west=3` | `(3,436,4,4)` |
| `t.west=4` | `(4,436,4,0)` or `(4,437,b,437)`, `b : Fin 3` |
| `t.east=3` | Start `(2,435,3,1)` |
| `t.west=2` | Start or `(2,434,2,0)` |

The seam East edge is in0..2, so it cannot supply East3. Its West edge is
one of the three squares0,1,4, so it cannot supply West2 or West3. Only these
three small square values are enumerated; there is no repeated reduction of
the full 430-action or 942-tile table. The head initializer retains south
color4, matching the actual decoded machine and earlier boundary packet.

`east_2_nonseam` and `west_4_nonseam` remove the seam alternatives only with
the explicit local condition `t.north≠437`. The general equivalences never
discard a seam. The focused checks construct genuine indexed-table witnesses
for every seam in both alternatives, using `Allowed.seam` and the proved
membership equivalence. In particular `(4,437,2,437)` simultaneously has
East2 and West4 and differs from both initializers. This supplies a concrete
negative control against omitting either seam exception.

Other focused checks prove the full conjunction forms
`Allowed t ∧ t.east=2` and `Allowed t ∧ t.west=4` equivalent to the displayed
alternatives, including admissibility in the reverse direction. They also
apply the exact color3 orientations to Start and the head initializer and
specialize West2 to arbitrary actual indexed tiles.

Fresh sequential commands, with Lean `v4.32.0`:

```sh
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942InitialHorizontal.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942InitialHorizontal.lean
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942InitialHorizontalChecks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942InitialHorizontalChecks.lean
```

Both final executions exited zero. The final main diagnostics are empty,
SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The checks log SHA256 is
`ec351371c4c9fb23aff52c5c4a280bb35aadcb8659c1a533d39bd76f036cfb0d`.
All eight theorem axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. Existing prerequisite objects were reused, not rebuilt.

Development history: the first main compile passed with two suggestions to
replace `simpa` by `simp`. Those two proof lines were simplified; the final
main and the first focused-check execution passed without diagnostics
other than the requested axiom reports. No mathematical premise changed.

Scope: these are local finite-language classifications only. There is no
whole-row, strip, periodicity, matching, machine-run, tiling, or halting
premise, and no such global conclusion is claimed. The bounded blank-strip
construction is a subsequent use of these local alternatives.
