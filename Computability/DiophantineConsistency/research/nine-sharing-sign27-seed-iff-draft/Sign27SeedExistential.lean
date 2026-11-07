import DiophantineConsistency.Sign27ReverseBridge

/-! SOURCE-ONLY: same-input existential equivalence; bridge import is uncompiled. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign27SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (x : V) :
    (∃ v : Fin 28 → V, v 0 = x ∧ InternalZero (SharingSeed27Sextic.seed p) v) ↔
    (∃ v : Fin 29 → V, v 0 = x ∧ InternalZero (SharingSeed28Sextic.seed p) v) := by
  constructor
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign27FirstCut.lift v, ?_, Sign27ZeroBridge.forward p v hz⟩
    simpa [Sign27FirstCut.lift] using hv
  · rintro ⟨v, hv, hz⟩
    obtain ⟨u, _, _, hzero⟩ := Sign27ZeroBridge.backward p v hz
    refine ⟨Sign27ZeroBridge.drop u v, ?_, hzero⟩
    simpa [Sign27ZeroBridge.drop] using hv
end DiophantineConsistency.Sign27SeedIff
#print axioms DiophantineConsistency.Sign27SeedIff.exists_same_input
