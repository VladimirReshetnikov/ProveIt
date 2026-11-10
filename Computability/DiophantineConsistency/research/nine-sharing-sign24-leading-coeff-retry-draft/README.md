# Sign24 leading-coefficient normalization retry

The prior attempt checked the N0 axis, diagonal-degree and other-residual
weighted-degree ingredients but its N0-square coefficient proof failed to
identify explicit `C 4` and `C 6` with polynomial numerals. This source-only
retry changes only that last module: the ring expansion uses natural scalar
multiples, and coefficient extraction uses the generic `coeff_smul` rule and
an explicit proof that the eighth monomial index is nonzero. It does not add
axioms or alter the arithmetic statement. The retained resource guards and
local heartbeat options are unchanged; elaboration remains untested.

Even if successful, this checks ingredients rather than a whole-expression
lower bound, and does not establish JSON/port-byte or PDF correspondence.
Independent prelaunch review and an assigned Lean slot are required.
