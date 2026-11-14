# Conditional preservation of internal derivation rules

`PA194RenameDerivationCases.lean` checks each of Foundation's ten internal
PA derivation-rule cases under a generic free-label renaming: logical axiom,
truth, conjunction, disjunction, universal and existential introduction,
weakening, shift, cut, and PA theory axiom. For rules with premises, each
result assumes internal PA `Derivable` for the appropriately renamed premise
context and concludes internal PA `Derivable` for the renamed conclusion.
The shift cases separately cover the two required map equations; universal
introduction uses the related lifted map and its eigenvariable equation.

The results apply to arbitrary model-internal contexts, formulas, and map
parameters, including nonstandard ones, with explicit well-formedness and
rule-membership premises in their theorem statements. They hold in every
nonempty candidate-PRA model with equality and an IΣ₁ arithmetic reduct, for
a supplied Σ₁ graph that correctly represents the parameterized map at every
model value. The PA axiom case uses the proven invariant of Foundation's
concrete `𝗣𝗔.Δ₁Class`. Lean reports `propext`, `Classical.choice`, and
`Quot.sound` for the printed dependencies, with no `sorryAx`.

These are individual conditional rule steps, not induction over arbitrary
internal derivations, an explicit primitive-recursive proof-code transformer,
an iPRA theorem, or a PA194 consistency implication. The bounded induction
invariant and its parameter closure remain to be established.

Run `check-rename-derivation-cases.sh` with the audited `IPRA_LEAN_OVERLAY`
and `IPRA_FOUNDATION_OVERLAY` set; it rebuilds the dependencies in a fresh
temporary overlay and rejects `sorryAx`.
