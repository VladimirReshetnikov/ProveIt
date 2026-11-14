# Equal-label gate witness groundwork

`PA194EqualGateWitness.collision_witness` strengthens the conditional
singleton witness inside PA. For any internally well-formed one-variable
formula `P`, any internally well-formed two-variable formula `D`, and any
model-valued label `a`, internal PA proves that some bit-set `s` satisfies

- `P(a) → bit(a,s)`; and
- for every `x`, `((bit(x,x) → (P(x) → bit(x,s))) →
  ((bit(x,s) → P(x)) → D(x,s))) → D(x,s)`.

This is the equal-label separation pattern, with `D` left arbitrary so the
actual code-1 translation can be used without treating it as literal falsity.
The proof uses the conditional singleton theorem and the internal PA proof
that bit membership is irreflexive. `tail_from_witness` separately proves the
generic internal PA inference from such a point/separation witness and
`∀s ¬E(s)` to the implication `(∀s (Sep(s) → Point(s) → E(s))) → C`, for
arbitrary internal formulas `Point`, `Sep`, `E`, and `C`.

`PA194RelativeFalseAll.internal_relative_false_all` supplies the needed
universal refutation when `E` is the actual code-1 translation after closing
any model-valued source label, including zero. The supporting
`PA194InternalBitDiagonalTerm` extends diagonal-bit refutation to every
internally well-formed model-valued term.

The witness and logical inference require an arithmetic model of IΣ₁;
`internal_relative_false_all` additionally uses the candidate-PRA model and
equality assumptions needed by the source closer. All input formula codes,
terms, and labels may be nonstandard. These are internal PA derivability
results. They do **not** yet identify the typed witness formulas with the
actual numerical equal-label separation-tail translation, establish the
full guarded-gate premise, prove an iPRA implication, or provide a finite
proof transformer. In particular, the remaining atom bridge must show that
Foundation's closer on the ordinary translated bit atom agrees with the
separately constructed closed-bit template for arbitrary model labels.

`check-equal-gate-witness.sh` is a full dependency rebuild requiring matching
audited `IPRA_LEAN_OVERLAY` and `IPRA_FOUNDATION_OVERLAY`. Because of disk
I/O pressure, the present check is a focused ordered suffix rebuild against
retained prerequisite objects; the full nested rebuild is deferred.

The author completed the focused ordered suffix rebuild with no `sorryAx`.
