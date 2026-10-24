# Reconstructing the compact54 assignment from the literal low mask

This checkpoint closes the sparse-assignment input to the previously checked
native convolution bridge. It does not assert the remaining global native
machine calibration or an object-language ZFC consistency biconditional.

The exact constants are the compact54 radix `ρ = 2^89` and cell length
`L = 4831`, so the cell width is `89L = 429959`. The support is precisely
`NativeLowPort54.positions`: the 520 frozen native assignment positions with
forbidden selector1 removed. Position507 is the distinguished two-bit dummy;
every other supported position has one bit. The low port is the whole
subtraction recipe, including the additional `2ρ^507` term.

## Checked interfaces

`NativeRadixDigits.lean` reconstructs the radix digits of `C−1` from a finite
origin mask, then increments exactly the origin digit. Its
`decode_originMask` produces the word equality, origin digit1, and all
capacity bounds. No assignment word or digit bound is supplied to that
lemma. `periodic_sum` proves the finite product reindexing for repeated
cells.

`NativeVariableMask.lean` proves the subtraction identity for arbitrary
finite support with a distinguished two-bit dummy. It proves that the
periodic cell mask, with the source's origin correction, has word
`cellWord × repunit + 1`.

`NativeSparseDigits54.lean` instantiates those results with the literal
compact54 positions. It reuses `OnePageLowPort54`'s exact support equality
and duplicate-free interval certificate; it does not rerun a large
pairwise position test. Its main statements are:

* `cellWord_eq_lowPort`: the capacity mask has exactly the frozen low-port
  subtraction recipe.
* `mask_word`: at `N` cells its decremented-origin mask word is
  `MC × repunit(429959,N) + 1`.
* `source_assignment`: positive literal old-z source zeros and a source
  window power yield `c` with word `C`, origin digit1, the exact periodic
  capacity bounds, and `c(k) ≤ 3` everywhere.
* `source_assignment_exists`: also extracts the positive cell count `N`
  from the source; no source window length or digit assignment is supplied.
* `assignment_sparse` and `assignment_boolean`: off-support digits are zero;
  every digit except dummy507 in each cell is Boolean. Selector1 is excluded
  explicitly by `selector_one_not_mem`.
* `source_sparse_convolution`: feeds the reconstructed assignment into
  `NativeWindowConvolution54.source_convolution_mask_digits`. The assignment
  word and bounds are no longer hypotheses of this combined theorem.

The coefficient interface remains explicit:
`NativeSourceMask.Interface ports 429959 NativeLowPort54.lowPort MF`.
It lists the exact beta, low/high mask port shifts, nonnegativity, bounds,
low-bit residues and population identity. This is arithmetic coefficient
information, not a supplied native-correctness proposition. The convolution
corollary also displays the remaining exact `K` stencil binding and the
finite high-mask word binding.

## Remaining boundary

The next native work is to bind the high mask to its periodic clean-band
mask, extract the local clause sums from the literal cyclic stencil, and
prove temporal phase alignment and global machine/tableau interpretation.
The already proved local decoder classifies an arbitrary Boolean selector
sum, so one-hot selection need not be assumed. Completeness/controller
calibration and interpretation in arbitrary ZFC models remain separate
obligations.

## Validation

The three main modules and their matching `Lean/checks/` files are checked
with the repository Lean4 toolchain. The ten generic axiom reports use only
`propext`, `Classical.choice`, and `Quot.sound` (some reports use a subset).
The literal decoder’s twelve public-API reports likewise contain only
those three axioms. Its sole compiler warning records that a symbolic
4831st power was deliberately left unevaluated. No new
axiom, `sorry`, native-machine correctness hypothesis, or internal-ZFC
reflection claim is introduced.
