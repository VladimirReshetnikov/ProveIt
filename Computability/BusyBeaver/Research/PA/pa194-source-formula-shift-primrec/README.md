# Primitive-recursive PA194 source formula shift and universal search

`formulaShiftCode` is an explicit total numeric function defined by recursion
on smaller formula codes. `formulaShiftCode_correct` proves that for every
actual Foundation PA194 source formula, at every binder depth, its output is
the code of the actual syntactic shift. The proof covers positive and negative
atoms, truth and falsity, both connectives, and both quantifiers.

The primitive-recursiveness proof builds a table of earlier outputs. Lean
checks the primitive-recursive table step (`tableStep_primrec`) and its exact
recursion equation (`tableStep_correct`), then derives
`formulaShiftCode_primrec` using `Primrec.nat_strong_rec`.

`codedSearch_primrec` gives an unconditional primitive-recursive search of a
list of numerical formula codes. On actual encoded source lists,
`codedSearch_selected` proves that the returned code is precisely the formula
chosen by `findPreimage` in the Foundation LK universal-rule compiler. This
removes the previous formula-`Primcodable` and numeric-shift PR premises from
that *search component*.

The checked theorems report `[propext, Classical.choice, Quot.sound]`, with no
`sorryAx`, in the ordered local dependency overlay. The nested standalone
script has not yet been replayed.

The algorithm is total but is only proved to agree with Foundation's shift on
codes of genuine source formulas; agreement on malformed inputs is not
claimed. This standard-Lean primitive-recursiveness proof does not encode the
whole LK derivation compiler, establish arithmetic internalization or a
nonstandard-model reduction, or calibrate the PA194 machine.

To rebuild the prerequisite chain from the repository root, set
`IPRA_FOUNDATION_OVERLAY` to the audited current Foundation object overlay and
run `bash Computability/BusyBeaver/Research/PA/pa194-source-formula-shift-primrec/check.sh`.
