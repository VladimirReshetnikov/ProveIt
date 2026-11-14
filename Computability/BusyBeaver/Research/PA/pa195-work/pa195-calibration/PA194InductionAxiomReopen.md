# Reopening induction-schema axioms

`PA194InductionAxiomReopen.lean` proves that closing any model-valued free
label at depth zero and then applying Foundation's `free` operation leaves
unchanged every code recognized by the concrete `InductionUnivR` predicate.
The result covers nonstandard internal formula codes and nonstandard universal
closures. The proof uses the predecessor result that such axioms are fixed by
closing, and proves an internal substitution lemma: substitution fixes a
well-formed formula when the vector agrees with bound variables up to the
formula's depth, even if the vector has one additional entry.

The result holds in every nonempty candidate-PRA model with equality and an
IΣ₁ arithmetic reduct. The printed dependencies are `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. This is equality of
formula codes for the particular close/reopen operation. Invariance for the
protected-prefix renamings needed in the quantifier and shift cases, the
finite Peano-minus axioms, and an internal derivation transformer remain open.
No machine/consistency implication is proved here.

Run `check-induction-axiom-reopen.sh` with the audited `IPRA_LEAN_OVERLAY`
and `IPRA_FOUNDATION_OVERLAY` set; the script rebuilds the closer dependencies
and the predecessor in a fresh temporary overlay and rejects `sorryAx`.

An independent fresh Linux replay passed with the audited overlays, rebuilding
the local dependencies and checking the displayed theorem axioms for `sorryAx`.
