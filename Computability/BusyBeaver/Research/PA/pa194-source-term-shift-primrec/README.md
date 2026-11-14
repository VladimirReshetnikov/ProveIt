# Primitive-recursive shift for PA194 source terms

The PA194 source language has no function symbols, so every term is a bound
or free variable. `termShiftCode` is an explicit primitive-recursive function
on natural numbers. `termShiftCode_correct` proves it maps every encoded
Foundation source term to the code of its actual syntactic `Rew.shift`.
`termShiftCode_eq_internal` identifies the same result with Foundation's
internal numeric `termShift language`, on codes of actual source terms.

The three theorems were checked against an ordered local dependency overlay;
each reports `[propext, Classical.choice, Quot.sound]` with no `sorryAx`.
A full nested standalone replay remains pending.

The agreement theorem concerns codes of actual source terms; no agreement on
invalid codes is asserted. This does not yet prove primitive recursiveness of
formula shift, the LK compiler, or a machine reduction, and it does not
internalize correctness in arithmetic.

To rebuild from the repository root, set `IPRA_FOUNDATION_OVERLAY` to the
audited current Foundation object overlay and run
`bash Computability/BusyBeaver/Research/PA/pa194-source-term-shift-primrec/check.sh`.
