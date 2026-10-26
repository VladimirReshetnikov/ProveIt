# Author receipt: propagating actual reset and finish rows

Date: 2026-10-26 UTC. Author: `controller_certificate`, at root's assignment.
Status: frozen; complete new main/check source self-read and fresh bounded
Lean compilation PASS. This is an author receipt, not an independent review.
Only the two new Lean files and this receipt were authored. Frozen sources,
maintained equations and shared status files were not modified.

All Lean source paths below are relative to `Lean/DiophantineConsistency/`.

| File | Lines | SHA256 |
| --- | --- | --- |
| `WangTiles942ResetRows.lean` | 162 | `c12f1209b1a90e967859a10e989b7fde9ae32bbcf8b6245f99ca267adcdf7513` |
| `WangTiles942ResetRowsChecks.lean` | 82 | `53df3940ba01e30572b97ddeaa879b1b670401badd29dc09bae0a70da2b82f8b` |
| Imported `WangTiles942ResetHorizontal.lean` | 92 | `1cba7e914d13a2d6053b5d35b7b308f08093ae99d36c8963952f0de05f663ebc` |
| Imported `WangTiles942Boundary.lean` | 201 | `efda0078ffa174d2d9905cbd3431479a94679479742bbf9ff5856d132b06313c` |
| Checks-only `WangTiles942StripGeometry.lean` | 90 | `2439e3e5bd3b9f4eeea38013e4a2e237444626cc5864b0244463be8a88ce4e7a` |

Circuit authored ResetHorizontal and Boundary. Root authored StripGeometry,
which imports this author's earlier InitialStrip. All complete imported
sources relevant to this packet had been read; the exact matching and local
classification interfaces were checked again before use. Both complete new
files were read before execution.

`ResetTile` means precisely one of `(1,438,1,p)` with
`p∈[434,435,436]`. `FinishTile` means precisely one of
`(0,432*a+b,0,438)` with `a,b : Fin 2`. Tuple order is
West/North/East/South. These predicates retain all possible bottom reset
labels and all four finish alternatives; uniform reset status does not
assert identical tiles.

`interval_propagate` proves connectivity of an arbitrary open integer
interval from one interior seed. It separately inducts over the natural
distance to the right and to the left. Integer-to-natural conversions are
made only after the corresponding order comparison. The theorem handles
negative coordinates, unequal distances to the walls, and a singleton
interior without an origin, periodicity or tile premise.

`reset_next` propagates a reset's east1 to the next tile's west1, using
the exact allowed/nonseam classification. `reset_previous` uses the
opposite edge in the opposite direction. `row_reset` combines these two
steps with interval connectivity. Its hypotheses are only allowedness at
each interior position, horizontal matching across interior edges, absence
of a north437 seam at each interior position, and one actual reset tile.
No facts at either wall or outside the interval are required. A separate
`row_reset_of_north438` obtains the seed reset from one actual north438 edge.

`strip_reset_row` keeps an arbitrary integer time fixed. Vertical matching
is not needed for that horizontal result.

The stronger `strip_finish_and_reset_of_south438` adds actual time matching
and starts from just one interior south438 edge at time `t`:

1. Time matching gives north438 at that position in row `t+1`.
2. Actual allowedness identifies the one reset there.
3. Horizontal propagation makes every interior tile in row `t+1` a reset.
4. Time matching pulls their north438 edges back to south438 at every
   interior point in row `t`.
5. The exact allowed-language classification identifies every original-row
   tile as one of the four finish tuples.

`strip_finish_and_reset_of_finish` exposes the equivalent trigger using
one actual `FinishTile`. Neither theorem assumes a head, machine run,
unique Start, existence of any other finish, or a uniform finish/reset row.
The explicit no-seam geometry is necessary: the actual seam
`(1,437,1,437)` has both horizontal colors1 but is not a reset.

The focused `marked_finish_trigger` check composes these conclusions with
root's frozen `PersistentStrip` and the exact signed marked plane. The
geometry provides nonseam at every interior point/time, and the existing
marked-word identities provide both matching orientations. Only one
south438 trigger remains. Further checks instantiate both directions of
integer propagation at a negative seed, a singleton interior, all reset
and finish parameter ranges, distinct bottom reset labels, and the actual
seam obstruction.

Fresh sequential commands with Lean `v4.32.0`:

```sh
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942ResetRows.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942ResetRows.lean
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942ResetRowsChecks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942ResetRowsChecks.lean
```

The original horizontal main passed its first execution. After adding the
requested finish-row consequences, the complete final main and checks
each passed their first execution. Final main diagnostics are empty:
SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The checks log SHA256 is
`4a35ea633ff8313eafdd3ef2c53383b1e7af0fce5673e0a16655584b6682fa47`.
All nine printed axiom reports use only `propext`, `Classical.choice` and
`Quot.sound`; the generic interval theorem uses no choice. No custom or
native-evaluation axiom occurs. Existing prerequisite objects were reused;
this is not a fresh dependency-closure compilation claim.

Final authored object SHA256s are
`44a6640fd7e8238d8c41f2983e0ae0bcd67e93fbcc68e3d0b9a7971e1a497b3c`
for the main and
`4bc0ef808cde9fcc4f310f29387bde468de39f5a550a2dc1d9d13f3ff5649be9`
for the checks.

Scope: this packet derives row propagation from one actual event. It does
not establish that a finish/reset event occurs, decode a machine step or
run, construct a reverse arithmetic witness, or close the consistency
equivalence. Those remain separate obligations.
