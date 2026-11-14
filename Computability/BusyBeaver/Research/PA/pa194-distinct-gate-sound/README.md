# PA194 distinct-label gate soundness

`PA194DistinctGateNumeric.distinct_gate_tail` discharges the remaining guarded
gate premise in every candidate-PRA model whose arithmetic reduct satisfies
IΣ₁. For arbitrary model-valued labels `a`, `b`, `c` with `a ≠ b`, `c ≠ a`
and `c ≠ b`, internal PA proves the translation of the negated numerical
separation tail. Labels, predicate codes and proof codes may be nonstandard.

The proof identifies the actual source-code translation with the typed general
gate witness. It checks the previously missing two-level closure of `bit(b,a)`
under the distinctness hypotheses and uses the existing exact translations for
the predicate, witness membership, and relative conjunction. The witness is
constructed by internal PA separation and conditional insertion. Together
with the previously checked equal-label case, this discharges the source gate's
logical premise. It does not connect the fixed modeled scheduler to the literal
PA194 Turing machine or prove an iPRA consistency direction.

`check-numeric-suffix.sh` rebuilds the numerical gate module with the audited
Lean and Foundation overlays and ordered prerequisite object directories in
`PA194_DISTINCT_NUMERIC_PREREQ_PATH`. Its suffix replay passed using separately
checked gate-closure, general-witness and retained deeper objects, and its axiom
audit contained no `sorryAx`. The full nested prerequisite chain was not
rebuilt by this suffix check.
