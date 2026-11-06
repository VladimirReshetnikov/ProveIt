import DiophantineConsistency.Sign33ResidualAssembly
import DiophantineConsistency.Sign33ResidualConverse

/-! Same-valuation equivalence for the abstract sign33 residual conditions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33ResidualIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem seed_zero_iff_all_cuts (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0))
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι (ports 1))
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι (ports 2))
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι (ports 3)) :
    InternalZero (SharingSeed33.seed p) v ↔ Sign33ResidualAssembly.AllCuts ports v := by
  exact ⟨Sign33ResidualAssembly.all_cuts_of_seed_zero p ports v hp0 hp1 hp2 hp3,
    Sign33ResidualConverse.seed_zero_of_all_cuts p ports v hp0 hp1 hp2 hp3⟩
end DiophantineConsistency.Sign33ResidualIff
#print axioms DiophantineConsistency.Sign33ResidualIff.seed_zero_iff_all_cuts
