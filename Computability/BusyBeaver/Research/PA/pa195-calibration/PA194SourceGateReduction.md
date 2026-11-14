# Conditional reduction of the guarded gate

`PA194SourceGateTargetLink.target_gate_from_tail` proves the precise remaining
conditional gate case needed by the target proof checker: for arbitrary
model-valued `a`, `b`, `c`, with `c ≠ a` and `c ≠ b`, an internal PA proof of
the translated negation of `PA194TargetGate.separationTailValue a b c`
yields an internal PA proof of the translation of
`PA194TargetGate.oldBundleValue a b c`. The theorem uses the checked exact
all-model identification of its source constructors with those target
values. `checkGate_and_fresh` also identifies the checker's successful result
with that same source gate code plus one.

`PA194SourceGateReduction.membership_vacuity` unconditionally proves the
translation of the membership-vacuity component under the two label
inequalities. The reduction handles the enclosing implications, including
the code-zero alias checks. `guarded_gate_if_tail` also covers a failed guard:
in that case the guarded source gate is zero, whose translation is provable.

The assumptions are a nonempty model of the candidate PRA language, with
equality, satisfying candidate PRA, whose arithmetic reduct satisfies IΣ₁.
All parameters, including the property code `c`, may be nonstandard. The
conclusion is Foundation's internal PA provability predicate. The negated
separation-tail premise is **not proved** here: it requires a model-uniform
internal PA comprehension proof for the translated formula, including
nonstandard formula codes. Fixed-complexity semantic comprehension does not
supply that proof. This package does not establish an iPRA theorem, a finite
proof transformer, or unconditional gate preservation.

`check-source-gate-reduction-suffix.sh` rebuilds the two new modules in a
fresh temporary directory and rejects `sorryAx`, using ordered prerequisite
object directories supplied in `PA194_GATE_PREREQ_PATH` plus the audited
`IPRA_LEAN_OVERLAY` and `IPRA_FOUNDATION_OVERLAY`. It is a suffix check: it
does not rebuild the source and target prerequisites.

The author ran the focused two-module suffix check against retained source
and target prerequisite objects. It passed with no `sorryAx`; the check did
not rebuild those prerequisites.
