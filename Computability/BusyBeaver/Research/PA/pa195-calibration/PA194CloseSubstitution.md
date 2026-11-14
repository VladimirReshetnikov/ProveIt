# Closing and substitution for internal templates

`PA194CloseSubstitution.close_formula_subst_fixed` proves, for any internally
well-formed arithmetic template with no free variables, that Foundation's
capture-avoiding closer commutes with substitution: closing the substituted
formula is the same as substituting the individually closed terms. The
internal formula, its bound depth, the substitution vector, and all model
labels may be nonstandard. The no-free-variable hypothesis is represented by
Foundation's shift-fixed equation, rather than a semantic truth predicate.
The proof checks term recursion, bound-variable lifting, vector recursion and
an internal formula induction.

`close_bitFormula` specializes this result to the actual translated source
membership atom. `close_bit_point`, `close_bit_twice_cross`, and
`close_bit_twice_diag` give the explicit one- and two-close bit formulas
needed in the equal-label gate branch; the cross-label equations assume the
two model-valued labels are distinct. These equations refer to the actual
Foundation closer and typed bit template, not just the separate closed-bit
constructor.

The assumptions are a nonempty candidate-PRA model with equality and an IΣ₁
arithmetic reduct. This is a syntax theorem, not yet an internal PA proof of
the numerical equal-label gate, an iPRA implication, or a finite proof
transformer.

`check-close-substitution.sh` is a full dependency rebuild requiring matching
audited `IPRA_LEAN_OVERLAY` and `IPRA_FOUNDATION_OVERLAY`. Because of disk
I/O pressure, the present check is a focused suffix rebuild against retained
prerequisite objects; the full nested rebuild is deferred.

The author completed the focused suffix rebuild with no `sorryAx`.
