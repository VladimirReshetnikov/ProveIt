# Internal PA proves numerical rho8 translations

`PA194SourceRho8Preservation.lean` proves that the positive arithmetic
translation of every numerical rho8 axiom is internally PA-provable in
every nonempty candidate-PRA model with equality and an IΣ₁ arithmetic
reduct. All four numerical parameters may be nonstandard. The theorem does
not need the source rule's `u ≤ a` guard, so it covers every permitted rho8
instance.

The proof constructs the relevant classical propositional derivation in
Foundation's internal PA calculus. When `c ≠ 0`, all implication codes needed
to expand the instance are nonzero, and their translated formulas have the
expected implication form. When `c = 0`, the proof uses the translated truth
code and a model-uniform consequence-introduction lemma, which handles the
`I(0,0)=0` alias explicitly. Lean reports `propext`, `Classical.choice`, and
`Quot.sound` for the printed dependencies, with no `sorryAx`.

This handles one concrete numerical seed-axiom family for the conditional
line-history theorem. The other numerical axiom families, the actual
machine-trace-to-lines bridge, object-theory iPRA transfer, and the PA194
machine/consistency equivalence remain open.

Run `check-source-rho8-preservation.sh` with the audited `IPRA_LEAN_OVERLAY`
and `IPRA_FOUNDATION_OVERLAY` set; it rebuilds dependencies in a fresh
temporary overlay and rejects `sorryAx`.

An independent fresh Linux replay passed with the audited overlays, rebuilding
the local dependencies and finding no `sorryAx` in the displayed theorem axioms.
