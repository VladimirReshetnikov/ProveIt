# Equal-label numerical guarded gate

`PA194EqualGateNumeric.equal_gate_tail` proves that, for every model-valued
`b` and `c` with `c ≠ b`, internal PA proves the translation of the actual
numerical negated separation-tail code `gateNeg (gateTail b b c)`.
`equal_old_bundle` derives the corresponding unguarded old-bundle result
under the same inequality, and `equal_guarded_gate` proves the actual guarded
gate translation for every `b,c`, including the guard-failure case `c=b`.

The model assumptions are a nonempty candidate-PRA model with equality whose
arithmetic reduct satisfies IΣ₁. The labels, property code `c`, and internal
formulas can be nonstandard. The conclusion is Foundation's internal PA
provability predicate. No full PA194 consistency/nonhalting implication or
iPRA theorem is asserted.

The proof identifies the actual numerical point and separation translations
with the previously checked typed collision witness. It uses the explicit
one- and two-close bit-atom equations, nonstandard source-code freshness, and
the universally refutable actual code-1 translation. The latter is kept as
its actual formula throughout; it is not replaced syntactically by falsity.

This establishes the equal-label case only. The nontrivial remaining gate
case has `a ≠ b`, `c ≠ a`, and `c ≠ b`; it still requires a model-uniform
internal PA bounded-comprehension proof for an arbitrary internal property
formula. The result does not supply a finite proof transformer.

`check-equal-gate-numeric.sh` is a full dependency rebuild requiring the
matching audited `IPRA_LEAN_OVERLAY` and `IPRA_FOUNDATION_OVERLAY`. Because of
disk I/O pressure, the present check is a focused suffix rebuild against
retained prerequisite objects; the full nested rebuild is deferred.

The author completed the focused suffix rebuild with no `sorryAx`.
