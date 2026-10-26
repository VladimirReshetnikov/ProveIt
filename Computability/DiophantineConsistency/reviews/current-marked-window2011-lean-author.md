# Current marked window: author implementation receipt

Date: 2026-10-26 UTC. Author: `controller_certificate`, at root's assignment.
This is an author receipt, not an independent peer review. Only the new main
module, its focused checks and this receipt were authored for this packet.
No frozen source, maintained equation, or umbrella import was changed.

Frozen source bindings:

| File under `Lean/DiophantineConsistency/` | SHA256 |
| --- | --- |
| `CurrentMarkedWindow2011.lean` (148 lines) | `b8df6733e6a812d31e251c817076671ce319927fd635731af3e88bab309585d3` |
| `CurrentMarkedWindow2011Checks.lean` (69 lines) | `0da5024cc6a44866be51dc659174e67c360bdfe753c3480eaba6b92bb1339ce6` |
| `CurrentOccupation2011.lean` | `6b3d2cd7ec4c3f9380b63ee1211e6e93138f4f4e265aa9e1f8f83ddef01e6b5f` |
| `CurrentTileColors2011.lean` | `c1f7fc6fda51795f182c0d14379206c781f8cdcae212e27ff5c0a9bede21b8f9` |
| `CurrentCellCoordinate2011.lean` | `6e316a7a9a0107e8bc2bc41bf2bcd5868251b297f0b5cd7c79b64a52da1e9f48` |
| `WangTiles942Periodic.lean` | `b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53` |

Root authored TileColors; complemented authored CellCoordinate; circuit
authored the generic Periodic packet. I read those complete main modules
and their checks before final execution, as well as both complete new
files. The new main was compiled only after the coordinate and color
packets were frozen and their author objects were available.

The exact displacement is retained as

```
bitShift v N = core.rank.toNat - 47*(N*2011)
stride v N   = (bitShift v N / 47) / 2011.
```

Neither value is replaced by a reduced representative or an independently
chosen stride. The ambient `NeZero N` requirement is derived from the
existing `NeZero (N*2011)` instance, not added as a native premise.

For each `j : ZMod N`, `assignment` chooses the actual selected tile in
the original physical cell `CurrentCellCycle2011.coordinate.symm j`.
`assignment_selected` preserves the full `Selected` predicate: its bit is1
and every other selector in that same original cell is0. Choice therefore
does not construct a new Boolean word or lose the existing source binding.

At coordinate0, the inverse-coordinate zero identity and the proved
`facts_start_selected` theorem force the chosen abstract index to be0.
Selection uniqueness is used only within that origin cell. The module
does not assert that Start occurs at only one coordinate.

The horizontal source identity is proved in the original full cyclic word:

```
coordinate.symm(j-1) = previousCell(coordinate.symm j).
```

The temporal source identity similarly uses the actual quotient:

```
coordinate.symm(j-stride) = temporalCell(bitShift)(coordinate.symm j).
```

After these bindings, the existing actual color lemmas give precisely
`East(j)=West(j-1)` and `South(j)=North(j-stride)`. The latter integer stride
cast in `MarkedWord` is explicitly reconciled with the natural quotient
cast. Whole-field alignment is derived from the original Facts inside the
proof; no phase, count, occupation, matching or tableau premise is supplied.

`facts_stride_nonzero` transfers the root color theorem's nonzero full-word
displacement to nonzero stride in `ZMod N`. The coordinate theorem cancels
the factor2011 in both representatives and the full modulus, so no inverse
of2011 moduloN or coprimality condition is needed. This also proves the
natural stride is positive. The marked-word predicate itself requires
only origin Start and the two matching conditions; nonzero and positivity
are separately exposed conclusions.

The principal `facts_marked_assignment` endpoint takes the original
`Facts v N x c carry digits` and returns an assignment with its full
selector binding, `MarkedWord N (stride v N : ℤ)`, nonzero cyclic stride,
and positive natural stride. The polynomial endpoint obtains one original
arithmetic window and augments those same `N`, source, word, carries and
digits with this assignment. There is no resampling of witnesses.

Focused checks include the exact expanded rank quotient, the zero value
of every nonselected selector, the sole-Facts endpoint, and the existing
signed plane pullback applied to this assignment in both matching
directions. They also show that an actual one-cell Facts window is
impossible because its temporal displacement would be zero; the earlier
generic one-cell coordinate and occupation theorems remain valid.

Fresh sequential commands, with Lean `v4.32.0`:

```sh
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentMarkedWindow2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentMarkedWindow2011.lean
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentMarkedWindow2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentMarkedWindow2011Checks.lean
```

Both final executions exited zero. Main diagnostics are empty, SHA256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The checks log SHA256 is
`929bbec673e3855384ad1f13fd4b51074770bafa63cb7d46693939bd60052a7f`.
All nine axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. Existing prerequisite objects were reused, not freshly
rebuilt by these commands.

Development history: the initial main compile reached a typeclass-search
timeout for `OfNat (Fin 942) 0`. Lowering the priority of the local helper
that derives `NeZero N` from `NeZero (N*2011)` prevented recursive numeral
instance search. No theorem, mathematical premise or conclusion changed;
the main and focused checks then passed.

Scope: the actual polynomial now yields a marked cyclic word in the exact
942-tile table with its actual positive temporal stride and original
selector binding. No coprimality or prescribed rectangular geometry is
assumed. Machine-run extraction, the reverse arithmetic construction and
the final consistency equivalence remain separate obligations.
