# PA194 source formula search in candidate-PRA models

`PA194SearchModel.lean` defines a fixed finite candidate-PRA code which searches a
pair-plus-one encoded stack for a formula whose Foundation source-language shift
is a given target. In every candidate-PRA model with an IΣ₁ arithmetic reduct,
`mismatch_model` identifies the code's equality test on internally valid source
formulas. `find_match` proves that if an entry below an arbitrary internal bound
has the required shift and every entry below the bound is an internally valid
formula, the code returns an index below the bound with the required shift.
Indices, bounds, and formulas may be nonstandard. The proof uses the established
internal bounded-search invariants and the fixed source-shift code; it does not
argue by external induction over the model's elements.

The validity condition is explicit. The remaining identification of this
pair-stack lookup with the exact Foundation sequent representation has not yet
been proved here. This result does not supply a coded compiler for nonstandard
Foundation proofs, establish PA/source-calculus calibration, or prove a machine
halting reduction.

The final module passed an ordered-overlay Lean 4.32 check against the freshly
rebuilt source-formula shift suffix and the audited project and Foundation
objects. Its printed axioms are `[propext, Classical.choice, Quot.sound]`; no
`sorryAx` was reported. The standalone nested replay below also passed with the audited overlays,
including the full source-formula-shift prerequisite chain.

From the repository root, using matching audited project and Foundation
objects, run:

```sh
IPRA_LEAN_OVERLAY=/path/to/project/lib \
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
  Computability/BusyBeaver/Research/PA/pa194-source-search-model/check.sh
```

The script uses temporary storage under `/dev/shm` by default, rebuilds its
source-shift prerequisite chain, and checks the reported final theorem axioms.
`TMPDIR` may be set to an alternative suitable temporary directory.

An independent suffix replay recompiled the final search module in a fresh
output directory against the independently recompiled source-formula shift and
the existing prerequisite overlays. Both printed theorems have the same axiom
report and no `sorryAx`; that suffix replay reused the prerequisite chains.
