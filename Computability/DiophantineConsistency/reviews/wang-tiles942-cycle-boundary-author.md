# Actual trace-cycle outer-edge formulas: author receipt

Status: **fresh Lean PASS**, 2026-10-26. Author: circuit-reduction agent. This is an author self-review/build receipt, not an independent peer review. The complete 104-line module and 63-line checks were read before final bounded builds. No frozen source or prerequisite object was changed.

## Frozen binding

Paths are relative to `Computability/DiophantineConsistency/` unless otherwise indicated.

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/WangTiles942CycleBoundary.lean` | `a2f992dbfd4c14d70b8daf423c0b598d714131c5605cf29c833bc7dc2b808f8f` |
| `Lean/DiophantineConsistency/WangTiles942CycleBoundaryChecks.lean` | `938cd83cf5a768a0c1a77f79cb6bb16b2f78b0caabe29f4ecca6ebf174c8aa65` |
| Repository `.lake/build/lib/lean/DiophantineConsistency/WangTiles942CycleBoundary.olean` | `744423edc6903da467f6cdd978fa000365dc6c6405641fe95e6577854d54f8f1` |
| `/tmp/wang-cycle-boundary-main.log` | `c11f3189426204e34cc44e9a6e6fbedb4ba6ec655505b4ac4a1f6aee6c36a73a` |
| `/tmp/wang-cycle-boundary-checks.log` | `ced55c113d673aed9ea61604b7d0fbb8efe5fbe26b60068bc398d540192e3c27` |

The sole main import is `WangTiles942TraceCycle`, frozen source SHA `58ca5b2877426faf6704700f970043526c50873f429e9248552d8bb3019ca17e`. Its earlier actual step, pass, and trace-bound constructions remain unchanged.

## Exact proof content

Namespace: `DiophantineConsistency.WangTiles942CycleBoundary`.

`runTile_outer_blank T hh t x hx` takes an actual halt statement `(DecimalMachine215.machine.run T).state = none` and an outer-position condition `x≤−(T+1)` or `T+1≤x`. It proves that the actual run row at any natural t is **exactly** `(0,0,0,0)` at x.

The proof invokes `halted_trace_box` for times t and t+1 with walls ±(T+1). These facts supply blank tape at x, exclusion of the old head, and exclusion of the next configuration's head. In the live case, the operational `step_eq` identifies the constructed moved head with that actual time-(t+1) head. Thus the receive branch is excluded as well as the transition branch. In the halted case the plain pass tuple follows from the actual color definition. There is no assumed clean-edge or normalized-tape premise.

`runTile_left_blank` and `runTile_right_blank` specialize this to `−L+1` and `R−1`, respectively, with separate natural bounds `T+2≤L` and `T+2≤R`. The margins are independent of each other and of cycle height.

`edgeCode k` is 2 when k=0, 1 when k+1=H and k≠0, and 0 otherwise. `edgeCode_le_two` makes it a valid Fin 3 seam parameter without assuming H positive beyond the supplied Fin H value.

`cycleTile_left_west T L hh hL k` proves

```
(cycleTile k (−L+1)).west = edgeCode k.
```

`cycleTile_right_east T R hh hR k` proves

```
(cycleTile k (R−1)).east = (edgeCode k)^2.
```

The initializer gives 2 on the left and 4 on the right; reset gives 1/1; finish gives 0/0; actual run rows give 0/0 by the established blank-tile result. The right initializer proof includes the R=2 possibility, where the first head initializer itself has east 4. `cycleTile_outer_edges` bundles both formulas. These edge equalities need no H≥3 or halt-to-height relation; those separate hypotheses remain required by the predecessor's complete Allowed/temporal cycle theorem.

The packet exposes the boundary formulas for a later seam band. It does not construct the seam band, quotient a plane, assert actual halting, or prove a full native/consistency converse.

## Focused checks

The checks verify the three row codes, distinguish the squared initializer edge 4 from the unsquared value 2, and show that every pair of codes gives one of the actual Allowed seam tuples. They permit arbitrary unequal extra widths and any Fin H index, without an extra height condition. Blank pass cells at the exact ±(T+1) boundaries hold at arbitrary later times.

A negative control shows why excluding only the old head would be insufficient: the actual first run row at position 1 is not the blank pass tuple, even though position 1 differs from the old head 0. Its south color is the actual receiving head color 4. This checks the substantive use of the next-head bound.

## Fresh bounded builds

```sh
lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942CycleBoundary.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942CycleBoundary.lean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942CycleBoundaryChecks.lean
```

Both final commands exited 0. Main: 3.78 seconds, peak 3,199,512 KiB, no Lean diagnostics. Checks: 3.22 seconds, peak 3,175,756 KiB, only seven intended axiom reports. `edgeCode_le_two` uses no axioms; the other reports use only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`, added axiom, or native-decision axiom occurs. Existing dependency objects were reused; no fresh replay of their full closure is claimed. The sole development correction closed three literal numeric tuple-projection goals with reflexivity after rewriting; no premise or mathematical statement changed.
