# Primitive-recursive shift for PA194 source atoms

`atomShiftCode` is an explicit primitive-recursive function on natural-number
codes. `atomShiftCode_rel` and `atomShiftCode_nrel` prove that it returns the
exact Foundation code of the shifted positive or negative atomic formula, for
each PA194 source relation and binary term vector. This composes the preceding
primitive-recursive binary-vector and term-shift results.

The three theorems pass a checked ordered local dependency overlay and report
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. A full nested
standalone replay remains pending.

Agreement is proved for genuine source atoms; no claim is made about other
formula codes. The unbounded-depth formula recursion, proof compilation and
correctness inside PA/PRA, and the PA194 machine calibration remain open.

To rebuild from the repository root, set `IPRA_FOUNDATION_OVERLAY` to the
audited current Foundation object overlay and run
`bash Computability/BusyBeaver/Research/PA/pa194-source-atom-shift-primrec/check.sh`.
