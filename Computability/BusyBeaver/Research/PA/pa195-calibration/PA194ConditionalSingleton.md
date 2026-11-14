# Conditional singleton witness in internal PA

`PA194ConditionalSingleton.conditional_singleton` proves the following
witness theorem inside Foundation's internal PA. For every internally
well-formed one-variable arithmetic formula `P` and every model-valued free
label `a`, PA proves that some bit-set `s` satisfies

`(P(a) → bit(a,s)) ∧ ∀x (bit(x,s) → P(x))`.

The arithmetic model must satisfy IΣ₁; both the code of `P` and `a` may be
nonstandard. This is an internal derivability statement, not evaluation of a
nonstandard formula by a truth predicate. The proof makes the `P(a)` versus
`¬P(a)` case split *inside PA*, using the fixed quoted singleton and empty-set
proofs. The singleton case uses the model-uniform equality-substitution
proof for the arbitrary internal formula `P`.

`PA194InternalEmpty` supplies the explicit internal PA proof that zero has no
bits. `PA194ConditionalSingletonLogic` checks the two logical transformations
that make the singleton and empty cases work. This witness is relevant to the
`a=b` guarded-gate case, but the present package does **not** identify it with
the actual numerical separation-tail translation or prove that gate. It also
does not prove arbitrary bounded comprehension, an iPRA implication, or a
finite proof transformer.

`check-conditional-singleton.sh` is a full dependency rebuild and requires
the matching audited `IPRA_LEAN_OVERLAY` and `IPRA_FOUNDATION_OVERLAY`.
Because of disk I/O pressure, the present check is an ordered suffix rebuild
of the three new modules against retained prerequisite objects; the full
nested rebuild is deferred.

The author completed the focused ordered suffix rebuild with no `sorryAx`.

An independent ordered suffix replay rebuilt all three modules against the
separately checked singleton and earlier source prerequisites. It passed
without `sorryAx`; the full nested replay remains separate.
