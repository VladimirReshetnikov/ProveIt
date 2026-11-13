import DiophantineConsistency.Sign31SeedPointwise

/-! UNCOMPILED existence equivalence preserving distinguished input. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign31SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (x : V) :
    (∃ v : Fin 32 → V, v 0 = x ∧ InternalZero (SharingSeed31Sextic.seed p) v) ↔
    (∃ v : Fin 33 → V, v 0 = x ∧ InternalZero (SharingSeed32Sextic.seed p) v) := by
  constructor
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign31FirstCut.lift v, ?_, Sign31ZeroBridge.forward p v hz⟩
    simpa [Sign31FirstCut.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign31CoordinateRecover.drop v, ?_, Sign31ZeroBridge.backward p v hz⟩
    simpa [Sign31CoordinateRecover.drop] using hv
end DiophantineConsistency.Sign31SeedIff
#print axioms DiophantineConsistency.Sign31SeedIff.exists_same_input
