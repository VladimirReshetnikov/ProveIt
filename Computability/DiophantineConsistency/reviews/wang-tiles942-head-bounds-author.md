# Actual stepped head stays inside the strip: author receipt

Date: 2026-10-26. Author receipt for two new sources, each completely read before the first bounded build. Both first builds passed. No existing source was edited.

| Source under `Lean/DiophantineConsistency/` | Lines | SHA-256 |
| --- | ---: | --- |
| `WangTiles942HeadBounds.lean` | 135 | `bed402c366871656a605ebef749451631c88b34ce57118fa6bea583fce700754` |
| `WangTiles942HeadBoundsChecks.lean` | 74 | `9787951e938a1b510d180b767e6359affbb9c460364bde2cd92f94b63742e538` |

The main imports these exact frozen sources:

| Import | SHA-256 |
| --- | --- |
| `WangTiles942OperatingRow` | `f92a15534d5bfdfedb124aef9dac8cc2660b4eacd78562be25066ce66c02e443` |
| `WangMachineAction` | `1776d84d82ae32ec58287779e639ce163bf0e10dec24056effc3aa4c2f1d3bd5` |
| `WangMachineStep` | `479ef25344a09804f3eeb6bd980e947941af55965ac48291349f90de14c3f100` |

Relevant structures were read in full: `WangTiles942RowEncoding` (`d9c24628856b55b6e91b843208539982810d84fbb6f2b5882382b61f4a3cb9df`) and `WangTiles942StripGeometry` (`2439e3e5bd3b9f4eeea38013e4a2e237444626cc5864b0244463be8a88ce4e7a`). Checks import only the new main. Both new modules set `Elab.async false` and `maxRecDepth 10000`.

## Statement and proof

`next_head_inside` takes only actual allowedness of every tile, actual horizontal matching `(T (x+1) t).west = (T x t).east`, an existing `PersistentStrip T N L R`, `RowEncodes T (-L) R t cfg`, and `cfg.state = some q`. It concludes that the head of the actual `DecimalMachine215.machine.step cfg` is strictly between the same walls. There is no temporal-matching, no-finish, next-state-live, or machine-calibration premise.

`inputIndex_eq` identifies the finite bit index used by the existing forced-head theorem with the Boolean index used by the actual machine action bridge. `head_transition` therefore supplies the exact transition tile at the current head. The direction-specific active edge is at least 6, from the actual target's membership and `valid_rail_range`. It is the East edge for a right move and West edge for a left move; the other edge is not claimed positive.

The literal right seam has West `a^2 ≤ 4` for `a : Fin 3`. The literal left seam has East `b ≤ 2` for `b : Fin 3`. If a right move landed on the right wall, the actual horizontal equation at the old head would equate its active East rail with that seam's West edge. If a left move landed on the left wall, the equation at `head-1` would equate the active West rail with the seam's East edge. Both contradict the numerical bounds. The already strict old-head bounds and exact one-cell movement then give strict successor bounds, not merely inequality with each wall.

The final movement formula is taken from the actual decimal-machine action bridge and generic `Machine.step` theorem. No assumption is made on the action's optional next state; movement into halt is included. No tape support, head uniqueness beyond the existing configuration representation, or decoded future row is assumed.

Focused checks instantiate both directional exclusions and the full bundled theorem with exactly these premises. A negative control checks that the first actual right-moving transition has West edge zero, excluding the incorrect stronger assertion that both transition edges have active-rail size. Separate finite seam comparisons retain both distinct wall bounds.

## Fresh verification

Commands from the repository root:

```text
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942HeadBounds.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942HeadBounds.lean
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942HeadBoundsChecks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942HeadBoundsChecks.lean
```

Both first attempts exited 0 without warnings. `/tmp/wang-tiles942-head-bounds-main-stage1.log` is empty, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. The check log `/tmp/wang-tiles942-head-bounds-checks-stage1.log` has SHA-256 `8502196034aec7f1dc7d1b7925191324039e5607ea450c07d11d7094c115afc0`. All 9 axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, new axiom or target-equivalence assumption was added.

This supplies the interior-head component of a future row-step theorem. It does not itself prove that the successor row encodes the step, nor a complete tiling/run or equation/consistency equivalence.
