import DiophantineConsistency.Sign32SeedPointwise

/-! UNCOMPILED existence equivalence preserving distinguished input. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32SeedIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_same_input (p : Fin 4 → ℤ) (beta x : V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta) :
    (∃ v : Fin 33 → V, v 0 = x ∧ InternalZero (SharingSeed32Sextic.seed p) v) ↔
    (∃ v : Fin 34 → V, v 0 = x ∧ InternalZero (SharingSeed33.seed p) v) := by
  constructor
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign32Substitution00.lift beta v, ?_, Sign32ForwardAssembly.source32_to_source33 p beta v hp0 hz⟩
    simpa [Sign32Substitution00.lift] using hv
  · rintro ⟨v, hv, hz⟩
    refine ⟨Sign32CoordinateRecover.drop v, ?_, Sign32ReverseAssembly.source33_to_source32 p beta v hp0 hz⟩
    simpa [Sign32CoordinateRecover.drop] using hv
end DiophantineConsistency.Sign32SeedIff
#print axioms DiophantineConsistency.Sign32SeedIff.exists_same_input
