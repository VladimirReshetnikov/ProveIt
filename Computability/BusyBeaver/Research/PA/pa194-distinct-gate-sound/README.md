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

`PA194ModeledHaltRefutesPA.modeled_halt_refutes_PA` composes the distinct and
equal-label gate proofs with the checked fixed modeled scheduler: in every
candidate-PRA model with IΣ₁ arithmetic reduct, if its modeled `haltAfter`
code returns 1 at an arbitrary model time, internal PA proves falsum. This
is unconditional on a separate gate-soundness assumption. It remains a
statement about the modeled scheduler; the nonstandard physical-machine trace
has not been linked to that scheduler. Neither literal-machine iPRA direction
follows yet.

A fresh two-module suffix replay passed without `sorryAx` using the independently
checked numerical witness and retained scheduler/gate prerequisite objects.
`check-modeled-halt-suffix.sh` reproduces that suffix with ordered prerequisite
objects. `check-modeled-halt.sh` additionally rebuilds the nested source and
scheduler endpoint chain but still requires separately supplied general-witness
prerequisite objects; a complete run of that wrapper remains in progress.

`PA194ModeledHaltIPRA.consistency_implies_modeled_nonhalt` transfers that
all-model result into the actual syntactic iPRA derivation
`Con(PA) → ¬Halt(modeled scheduler)`, where the halting sentence existentially
quantifies a time at which the fixed primitive-recursive `haltAfter` code
returns 1. This proves a direction for the auxiliary modeled scheduler, not
for the literal 194-state Turing machine. In particular, neither requested
machine-specific iPRA direction is established by this theorem.

A fresh theorem suffix check passed without `sorryAx`, using the rebuilt
100-module PA refutation-certificate chain, rebuilt transfer and refutation
bridges, and retained scheduler/gate prerequisites. The full nested chain was
not rerun as a single successful script: a first combined attempt rebuilt the
certificate but encountered a missing module in its temporary overlay; the
missing modules and transfer objects were rebuilt in a corrected overlay before
the theorem was checked. `check-modeled-ipra-suffix.sh` reproduces the final
check with the audited Lean and Foundation overlays and ordered prerequisite
objects in `PA194_MODELED_IPRA_PREREQ_PATH`.
