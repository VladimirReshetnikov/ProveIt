# Binary internal source-preimage code

`preimageCode : Code 2` is a fixed finite candidate-PRA code taking a
Foundation bit-coded formula set and a target. It applies the direct bounded
set search from `pa194-source-set-search`, using the set code itself as the
bound. In every candidate-PRA model whose arithmetic reduct satisfies IΣ₁,
`preimage_correct` says that if the input is an `IsFormulaSet` and the target
is a member of its `setShift`, the result is a member of the input set whose
shift is the target. The set and formula codes may be nonstandard.

`preimage_graph_correct` establishes the same conclusion from the actual
parameter-free Σ₁ graph of this fixed code, allowing the result to be used in
internal arithmetic constructions. The bit characteristic code was selected
once using a candidate-PRA existence proof; the theorem is for that fixed
choice throughout all covered models.

This is a source universal-rule search component. It does not give a complete
coded derivation traversal, a proof compiler, PA/source-calculus calibration,
or a machine halting reduction.

The final module passed a fresh Lean 4.32 suffix rebuild against the freshly
rebuilt set-search and source-shift suffixes and the audited project and
Foundation objects. Its printed theorem axioms are `[propext, Classical.choice,
Quot.sound]`, with no `sorryAx`. A full nested replay of this package is
pending; the source-shift prerequisite has passed its own full replay, while
other prerequisite replays were running when this package was prepared.

From the repository root, with matching audited project and Foundation objects:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-source-set-search-root/check.sh
```

The script rebuilds the prerequisite chain under `/dev/shm` by default; set
`TMPDIR` for another suitable temporary directory.

An independent suffix replay recompiled this root module in a fresh output
directory against separately checked set-search and formula-shift objects,
reusing the other prerequisite overlays. It reported no `sorryAx`.
