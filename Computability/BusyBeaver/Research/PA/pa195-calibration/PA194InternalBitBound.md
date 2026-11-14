# Internal PA bit-position bound

`PA194InternalBitBound.internal_PA_bound_explicit` proves, in every IΣ₁
arithmetic model and for every model-valued free label `a`, that internal PA
proves `∀x (bit(x,a) → x<a)`. The model and label may be nonstandard. It
obtains a fixed IΣ₁ proof from the standard arithmetic-model bit bound, quotes
that proof into internal PA, and specializes it at the model label. The code
also proves the exact typed substitution equation for the bit and order
formulas used in that statement.

This is an ingredient for deriving separation over a bit-coded set from the
internal bounded-comprehension theorem. It does not yet establish separation,
the numerical gate, a connection to the physical machine, or either iPRA
consistency implication.

The module passed an independent suffix replay against separately checked
singleton and retained prerequisite overlays; the theorem axiom audit had no
`sorryAx`. The full nested prerequisite chain was not replayed. Run
`check-bit-bound-suffix.sh` with the audited Lean and Foundation overlays and
`PA194_BIT_BOUND_PREREQ_PATH` set to the ordered prerequisite objects.
