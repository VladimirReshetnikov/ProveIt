# Internal PA separation on bit-coded finite sets

`PA194SeparationWitness.internal_separation` proves that, in every IΣ₁
arithmetic model, for every internally well-formed one-variable formula `P`
and every model-valued free label `a`, internal PA proves

```
∃s ∀x (bit(x,s) ↔ (bit(x,a) ∧ P(x))).
```

The formula code, label, and proof codes may be nonstandard. The proof applies
internal bounded comprehension to `bit(x,a) ∧ P(x)` with bound `a`, and uses
the internal PA proof that `bit(x,a)` implies `x<a`. It lifts the pointwise
logical equivalence under the universal quantifier and then constructs the
existential witness within the internal proof system.

This establishes a general internal separation theorem. It does not yet
identify its formula with the remaining numerical gate, connect the modeled
scheduler to the literal PA194 table, or prove either iPRA consistency
implication.

A fresh ordered suffix replay rebuilds the four local modules using separately
checked bounded-comprehension, bit-bound and retained prerequisite objects; the
axiom audits contain no `sorryAx`. The full nested prerequisites have not been
rebuilt by this suffix checker. Run `check-internal-separation-suffix.sh` with
the audited Lean and Foundation overlays and the ordered prerequisite object
directories in `PA194_SEPARATION_PREREQ_PATH`.
