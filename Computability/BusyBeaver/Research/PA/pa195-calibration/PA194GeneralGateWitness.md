# Internal PA witness for the separation gate

`PA194GeneralGateWitness.witness` proves, in every IΣ₁ arithmetic model, that
internal PA proves existence of a bit-coded set `v` with these properties for
arbitrary model labels `a`, `b` and internally well-formed formula `P`:

* `P(b) → bit(b,v)`;
* for every `x`, `bit(x,a) → P(x) → bit(x,v)`;
* for every `x`, `bit(x,v) → P(x)`.

The last two clauses are encoded with the gate's relative conjunction, using
an arbitrary internally well-formed formula `D` as the conjunction's target.
The model, labels, formula and proof codes may be nonstandard. The proof first
constructs the subset of `a` selected by `P`, then conditionally inserts `b`
when `P(b)` holds. Equality replacement and an explicit internal proof of
reflexivity provide the designated-element case.

This is the abstract witness needed by the distinct-label gate. It does not
itself identify these typed formulas with the concrete numerical source gate,
connect the modeled scheduler to the literal PA194 table, or establish an
iPRA consistency direction.

Run `check-general-gate-witness-suffix.sh` with the audited Lean and Foundation
overlays and ordered prerequisite object directories in
`PA194_GATE_WITNESS_PREREQ_PATH`. The suffix checker rebuilds all five local
modules and audits their printed axioms for `sorryAx`; it does not rebuild the
full nested prerequisite chain.
The five-module suffix replay passed against separately checked separation and
retained deeper prerequisites; the printed axioms contain no `sorryAx`.
