# Actual 942-tile local signal matching: author receipt

Status: **fresh Lean PASS**, 2026-10-26. Author: circuit-reduction agent. This is an author self-review and build receipt, not an independent peer review. The complete 128-line module and 86-line checks were read before the final bounded compilations. Only these new source files, their new object, and this receipt were written for the packet; no frozen dependency was changed.

## Frozen files

Paths are relative to `Computability/DiophantineConsistency/` unless absolute.

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/WangTiles942Signals.lean` | `c678e98715e3ef8fa32f179275ba299f3d49256176510821c17056686ba76650` |
| `Lean/DiophantineConsistency/WangTiles942SignalsChecks.lean` | `01aae495b5eb8645d783473ebce3f21c2c68283a5641db6987864689988a0db9` |
| Repository `.lake/build/lib/lean/DiophantineConsistency/WangTiles942Signals.olean` | `cd065628bc3bf138f60b2b023c28e6beb11152e2924bc4ea0893b4fedba17ced` |
| `/tmp/wang-signals-main.log` | `fb89362f70e8b1c552bb3b59b94df0debd20682008b81448576243fc0d289862` |
| `/tmp/wang-signals-checks.log` | `a953211e2503f968e882e76930c0327881034b915d93cc41a6730b8c5b1d51a7` |

The module imports only `DiophantineConsistency.WangTiles942InputLanguage`, frozen source SHA `a28c66e285b3fc652392bc9d58c04135a4fef1f11b4a7e4378a0e02a4416307c`. It reuses the actual target membership, target-restricted rail injectivity, and disjoint directional rail ranges from Language. It does not introduce a second action table or a new rail calibration.

## Exact theorem scope

In namespace `DiophantineConsistency.WangTiles942Signals`:

- `plain_east_eq_zero_or_left_receive` and `plain_west_eq_zero_or_right_receive` classify the only possible nonzero edge of an Allowed plain-input tile. The alternatives retain pass, finish, and the opposite receive orientation as zero-edge cases. Every nonzero receive target comes with membership in the corresponding actual target set.
- `plain_east_small_eq_zero` and `plain_west_small_eq_zero` prove that an edge below 6 is zero. Thus actual seam colors, at most 4 horizontally, cannot absorb a nonzero receive signal.
- `plain_pair_edge_zero` takes two Allowed tiles with specified plain north bits and their exact east/west equality. A nonzero east edge of the left tile is a left-direction rail, while a nonzero west edge of the right tile is a right-direction rail. Their actual ranges are disjoint. Both receive/receive and receive/zero possibilities are excluded without assuming head uniqueness or row semantics.
- `right_transition_receiver` takes an actual action index, its direction `true`, an Allowed plain-input right neighbor, and equality of the transition's east edge with the neighbor's west edge. It returns the complete literal tuple `⟨rail true target, bit, 0, headColor target bit⟩`, where `target = (action j).2.2`.
- `left_transition_receiver` is the exact left counterpart: equality of the left neighbor's east edge with the transition's west edge returns `⟨0, bit, rail false target, headColor target bit⟩`.
- Both receiver proofs establish action-target membership before using injectivity restricted to the actual direction-specific target set. Neither requires `target < 215`; halt target 215 is retained.
- `plain_zero_edges_iff_pass_or_finish` retains exactly the pass and finish alternatives. `plain_zero_edges_nonfinish` selects pass only with the explicit additional premise `t.south ≠ 438`.

All statements are local finite-language implications. They do not assert existence of an adjacent matching pair, uniqueness of a head in a row, a machine step, a running strip, eventual halt, or the consistency equivalence.

## Focused checks

The checks instantiate the paired-edge theorem on arbitrary actual table entries and test receive/receive range incompatibility. They recover the literal neighbor tuple for actual action 0 (right, target 1, output head 4), action 5 (left, target 4, output head 11), and actual halt-target action 125 (right, target 215, output head 433). These small numerical equalities use kernel-checked decisions against the existing authenticated data.

An explicit family of Allowed zero-edge plain finish tiles proves that the nonfinish premise cannot simply be removed. A final check combines arbitrary plain inputs, horizontal colors at most 4, and the nonfinish premise to obtain the exact pass tile.

## Fresh bounded compilation

```sh
lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942Signals.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942Signals.lean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942SignalsChecks.lean
```

Both final commands exited 0. Main: 3.51 seconds, peak 3,194,940 KiB, no Lean diagnostics. Checks: 3.48 seconds, peak 3,180,660 KiB, only the nine intended axiom reports. Every reported theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`; no new axiom, `sorryAx`, or native-decision axiom appears. Existing dependency objects were reused; no fresh replay of their complete closure is claimed.
