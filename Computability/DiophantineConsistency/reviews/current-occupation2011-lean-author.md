# Current occupation: author implementation receipt

Date: 2026-10-26 UTC. Author: `controller_certificate`, at root's assignment.
This is an author receipt, not an independent peer review. Only the two new
Lean files and this receipt were authored for this packet. Frozen sources,
maintained equations and umbrella imports were not edited.

Frozen source bindings:

| File under `Lean/DiophantineConsistency/` | SHA256 |
| --- | --- |
| `CurrentOccupation2011.lean` (141 lines) | `6b3d2cd7ec4c3f9380b63ee1211e6e93138f4f4e265aa9e1f8f83ddef01e6b5f` |
| `CurrentOccupation2011Checks.lean` (62 lines) | `d4f24e70405b2e890775c59535c429048bbfcab28fa0cf96b006b3f990d2a906` |
| `CurrentWholeField2011.lean` | `16c06800d326578b5898f2353229b574f2c0c8783bfadc362d517d34d2a5d079` |
| `CurrentAdjacency2011.lean` | `160cef12e27cda2ece581ba0acfb2fcbbf194d918fe75d630705a7feb8e97133` |
| `WangTiles942Language.lean` | `a28056b4929cfea69255619b5d89b5f7a64dc47efe0e94ca2e43e00f7788228d` |
| `CurrentCellCycle2011.lean` | `874a68dc11255170f19dc1a5345e195f36379711f8af630b16dd6eb9fe77081d` |

I read the complete Language, CellCycle and CellLabels sources before
implementation, following the full WholeField review and Adjacency
authorship. Both new files were read in full before their execution. The
CellCycle source/object was frozen before the new module was compiled.

`Occupied c b` means that there exists an actual abstract index `i : Fin 942`
with `Selected (selectorValue c b) i`: that selector is1 and all other
selectors at the same cell are0. The public `facts_occupied` theorem proves
this for every aligned `Cell N` from the original `Facts v N x c carry digits`
alone. It has no supplied phase, alignment, label, occupation, marker-value,
unique-Start, or tableau premise.

The proof explicitly uses the true packed horizontal orientation. `westWord`
is the eight-bit block starting at978; `eastWord` starts at969. Aggregating
the eight actual copy equalities proves

```
eastWord c b = westWord c (b-2011).
```

`facts_horizontal_words` derives whole-field alignment internally through
`facts_whole_field` and applies the actual Adjacency endpoint to the same
word and carry functions. This aggregation does not yet interpret either
word as a tile color.

`facts_start_selected` applies the decoded origin clause to the forced
physical selector0 and its proved abstract index0. The empty case is
impossible because that bit is1; the occupied case's selection uniqueness
identifies its tile with the actual Start index. This establishes the base
of the spatial propagation without assuming Start occurs only once.

For the induction step, an occupied cell's decoded word has West block
`255-(tile i).west`. `WangTiles942Language` proves every actual horizontal
color is below250, so that complement is strictly positive. The horizontal
copy gives the same positive number as the East block of the spatial
successor. That successor's decoded empty case would force every copied
block, in particular its East word, to be0. The contradiction leaves its
actual occupied case. The step uses the exact identity
`previousCell(next b)=b` in the full `ZMod (N*2011)` word.

The generic `CurrentCellCycle2011.propagate` theorem reaches every aligned
cell from zero by adding2011. It covers the one-cell case and retains the
same original Boolean word. The proof does not replace the temporal shift,
reconstruct a new word, or require a positive temporal stride.

`facts_selectorCount_eq_one` then evaluates the actual selected-index sum
with constant weights1. The focused checks also transfer this result to
the full physical `Fin 942` sum, using the established actual permutation.
Other checks prove the selected index is unique within each cell, include
`N=1`, check Start's exact horizontal complements253 and252, and exhibit why
the weaker bound color<256 would not alone exclude a zero complement.

`polynomial_zero_occupied_window` starts with the actual positive
fourteen-variable polynomial zero. It obtains one arithmetic window and
augments those original witnesses with occupation. A global chosen tile
assignment is intentionally left to the next composition.

Fresh sequential commands, with Lean `v4.32.0`:

```sh
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentOccupation2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentOccupation2011.lean
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentOccupation2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentOccupation2011Checks.lean
```

Both passed on their first execution, with no source correction. The main
diagnostics are empty, SHA256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The checks log SHA256 is
`f3b080fee783b477e1e9f05ab4c0c29a21213496189b9ac87952426b676d61d1`.
All seven reported theorem axiom sets contain only `propext`,
`Classical.choice`, and `Quot.sound`; no new or native-evaluation axiom is
introduced. Prerequisite objects were reused, not freshly rebuilt here.

Scope: every aligned cell now selects exactly one actual tile. Matching
tile colors, a native Wang window, positive temporal stride, finite-language
machine semantics, the reverse existence construction and the final
consistency equivalence remain separate obligations.
