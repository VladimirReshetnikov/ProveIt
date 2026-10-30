# Literal ZFC consistency: remaining witness-bound obligation

Write `ρ` for `FoundationHAConsistencyNormalization.rho`, the actual Foundation
ZFC refutation sentence, and `conB ρ` for
`StrictPiTwoBridge.conB ρ = ∀ b, ¬ bnd ρ(b)`. The bounded transformation has a
proved implication `bnd ρ(b) → ρ` in every arithmetic structure. Consequently,
`PRAConBForward.PRA_proves_forward` has compiled provisionally as an actual
candidate-PRA proof of the mapped implication `¬ρ → conB ρ`. This is the easy
direction of the comparison; the converse has **not** been proved.

The concrete remaining task is to prove in candidate PRA that any actual
Foundation refutation supplies a common bound for *every* existential witness
introduced by the `bnd` transformation. One sufficient interface would be:

1. a unary candidate-language open predicate `R(d)` for a coded refutation and
   an actual candidate-PRA proof of `lMap ρ → ∃ d, R(d)`; and
2. a unary primitive-recursive code `B` and an actual candidate-PRA proof of
   `∀ d, R(d) → (lMap (bnd ρ))(B(d))`.

The two proofs would yield `conB ρ → ¬ρ`: if `ρ` held, the first supplies a
code `d` and the second supplies the prohibited bound `B(d)`. Together with the
provisional forward implication this would identify the strict surrogate
with the **literal** Foundation consistency sentence in candidate PRA. Neither
proof, the predicate `R`, nor the code `B` has yet been constructed. A variant
may use a finite tuple of separately supplied certificate values, but must
retain a proved coverage statement and bound *all* nested witnesses uniformly.

A plausible construction is to compile an explicit primitive-recursive
refutation validator, then use primitive recursion and bounded maximization to
compute a bound on its intermediate sequence codes and on the witnesses for
every boundedly quantified check. The existing bounded-search and characteristic
compilers can supply parts of such a construction. The main missing proof is
that the validator and its proposed bound represent Foundation's **actual**
`provabilityPred` in every candidate-PRA model, including nonstandard models.
Foundation's proof predicate uses a Σ₁ fixpoint/sequence definition; in
particular `Blueprint.cseqDef` contains bounded universal quantifiers whose
bodies involve Σ₁ subformulas. It is therefore not justified to pass it directly
to the existing positive-formula or Σ₀ characteristic compiler. Standard-Nat
correctness or an IΣ₁ proof of `ρ ↔ ∃ b, bnd ρ(b)` would not by itself prove
the required candidate-PRA equivalence.
