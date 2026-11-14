# Primitive-recursive shift for PA194 binary source-term vectors

Every PA194 source relation has arity two. `vec2ShiftCode` is an explicit
primitive-recursive function that shifts both terms of an encoded binary
vector. `vec2ShiftCode_correct` proves that it exactly matches Foundation's
`Matrix.vecToNat` encoding of the shifted vector, for every actual pair of
source terms. It builds on the preceding primitive-recursive source-term shift.

The two theorems were checked against an ordered local dependency overlay and
report `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. A full
nested standalone replay remains pending.

This establishes the binary vector operation only. Primitive recursion for
formula shift, proof compilation and correctness inside PA/PRA, and the PA194
machine calibration remain open.

To rebuild from the repository root, set `IPRA_FOUNDATION_OVERLAY` to the
audited current Foundation object overlay and run
`bash Computability/BusyBeaver/Research/PA/pa194-source-vector-shift-primrec/check.sh`.
