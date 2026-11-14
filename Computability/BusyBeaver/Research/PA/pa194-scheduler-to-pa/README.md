# Conditional modeled-scheduler halt to PA refutation

`PA194SchedulerToPA.lean` composes the coded scheduler's model-length
iteration theorem with the target-to-PA translation. In every candidate-PRA
model whose arithmetic reduct satisfies IΣ₁, `modeled_halt_refutes_PA` proves
that if the modeled initial scheduler's halt bit is one after a model number
of steps, then the model contains a PA derivation of falsum.

The theorem has one explicit mathematical premise: for every guarded
oldBundle instance (`c ≠ a` and `c ≠ b`), its source translation is internally
PA-provable. All other seed cases, the target proof rules and the model-length
invariant are discharged by the imported theorems. The total scheduler
iteration continues mathematically after halt; the hypothesis asks only for a
step at which its halt bit is set.

The coded scheduler has been matched to the source scheduler on standard
natural inputs, but its nonstandard iteration is **not** yet identified with
a literal PA194 controller or machine trace. The remaining guarded oldBundle
premise is also unproved. `modeled_halt_refutes_PA_of_tail` replaces it with
the more specific fresh-label negated separation-tail premise established as
sufficient by the gate reduction. Consequently, this is not yet a PA194/Con(PA)
implication in PA or PRA.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-scheduler-to-pa/check.sh
```

The final module was rebuilt against the refreshed target-to-PA bridge,
freshly checked scheduler iteration and retained source/prerequisite overlays.
A full nested replay of this wrapper has not yet been completed. Its printed
axiom dependencies contain no `sorryAx`.

An independent suffix replay rebuilt the conditional endpoint against the
separately checked iteration and target-to-PA objects and retained deeper
prerequisite overlays. It passed without `sorryAx`; this was not a full nested
replay.

A fresh ordered suffix replay rebuilt this module and the halt-code endpoint
after adding the separation-tail variants; it passed without `sorryAx`, using
retained checked prerequisite overlays.
