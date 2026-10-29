# Recovered adaptive power

The actual current natural zero now yields `X = Exp.exp R` in every selected
`IΣ₁` model, where the represented exponential `Exp.exp` is base two and `R`
is the actual adaptive rank. The proof first derives `X ≥ 16` from `q | 3X`
and the fixed radix-47 port. The exact first and main Pell indices then permit
the existing internal paired-growth argument to show `Exp.exp R < Y`.

The main signed root and the first-index quotient give a second additive
projection. Combining it with the represented main Pell coordinate yields
`3X ≡ 3·Exp.exp R (mod 4a+3)`, where `a=Y(X+1)`. Both `3X` and
`3·Exp.exp R` lie strictly below that modulus, so they are equal; cancellation
of the explicit nonzero factor 3 gives the displayed power identity. The proof
never assumes `q | X` or cancels 3 modulo q.

This is still a forward arithmetic consequence, not the complete HA
proof-existence theorem. In particular the adaptive radix/source binding,
reverse witness construction, and internal syntactic equivalence remain open.
