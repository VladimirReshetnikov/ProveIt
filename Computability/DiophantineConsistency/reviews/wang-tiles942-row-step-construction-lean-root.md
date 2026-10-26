# Forced actual row evolution and explicit reverse step row

Date: 2026-10-26. ROOT independently read every line of both new main/check
packets and both author receipts before four fresh direct Lean runs. All
four passed. Author objects supply the check imports; fresh main outputs
were written separately under `/tmp`. Existing dependency objects were
reused, without a complete closure or umbrella rebuild claim.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942RowStep.lean (205 lines) | f4b6f60e4dece143de6d45120c8aa8ae84691d50b1b888e6e0dcb0226f17f84b |
| WangTiles942RowStepChecks.lean (86 lines) | 29cd6e8dc012c9d0d65fc9f18d2b58fcea3de8fc996d38b4499c68bf74b65fe9 |
| WangTiles942StepConstruction.lean (159 lines) | 935bfb4b2762bd099185350f3869114c81f11140a823951e6319a33ce292138f |
| WangTiles942StepConstructionChecks.lean (114 lines) | 5e8c6382fceabcf880ca431af455cb71d90350b107c10f5c748eb3a4dd688a92 |

`row_step` derives the next row encoding from actual Allowed tiles,
horizontal/time matching, the persistent strip, current encoding and a
live state. At the old head the forced transition writes its Boolean.
At the moved head the exact directional signal forces the actual target
and old destination bit. At every other cell both edges are zero: a
neighbor is a bounded seam, another plain input, or the inactive side of
the actual transition. The separately proved operating-row exclusion
removes finish, forcing pass. The actual step's three-way color formula,
strict next-head bounds and time matching finish the proof.

The theorem assumes neither no-finish nor a desired row-step assertion.
It permits actions entering halt215. Focused checks obtain north432/433
at that moved head, specialize to arbitrary marked words, and derive the
actual clock2 encoding from the literal clock1 initialization.

Conversely, `step_row cfg q hq` explicitly constructs a whole-integer
matching row from an actual operating configuration. It places the
literal transition at the old head, its exact receiver at the moved head
and a plain pass elsewhere. Every tile is actually Allowed; north equals
the original encoder and south equals the actual machine-step encoder.
The complete west/east formulas prove matching in both move directions.
No finite geometry, external row encoding or target-not-halt hypothesis
is supplied. Tests cover first blank action, actual left action5 and
actual halt action125 at negative coordinates with duplicate tape entries
and a destination bit already one.

Commands used `lake env lean -M6000 -j1`. Both main logs are empty.
The ten RowStep axiom reports contain only standard axioms; check log
SHA-256 `6e3f356b31b8c58bc4e3f4c077b0bd23ea7a83e2912ecdd05285a6946d985c86`.
The thirteen StepConstruction reports likewise contain only standard
axioms; check log SHA-256
`336c76d27977b345d6778f3dab610edf730b493cbdf056326276933c5dcdbf99`.
The only axioms are subsets of `propext`, `Classical.choice`, `Quot.sound`.

Author receipts: [forced row step](wang-tiles942-row-step-author.md) and
[constructed step row](wang-tiles942-step-construction-author.md).
Periodic halting extraction, a complete cofinal reverse tiling,
controller completeness and the internal-ZFC proof are separate work.
The maintained decimal equation page is unchanged.
