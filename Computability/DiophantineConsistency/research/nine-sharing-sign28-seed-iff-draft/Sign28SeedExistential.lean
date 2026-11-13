import DiophantineConsistency.Sign28SeedPointwise

/-! SOURCE-ONLY candidate; no Lean elaboration has been run. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (beta x : V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (∃ v : Fin 29 → V, v 0 = x ∧ InternalZero (SharingSeed28Sextic.seed p) v) ↔
    (∃ v : Fin 32 → V, v 0 = x ∧ InternalZero (SharingSeed31Sextic.seed p) v) := by
  constructor
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign28FirstCuts.lift beta v, ?_, Sign28ZeroBridge.forward p beta v hp0 hz⟩
    simpa [Sign28FirstCuts.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign28CoordinateRecover.drop v, ?_, Sign28ZeroBridge.backward p beta v hp0 hz⟩
    simpa [Sign28CoordinateRecover.drop] using hv
end DiophantineConsistency.Sign28SeedIff
#print axioms DiophantineConsistency.Sign28SeedIff.exists_same_input
