import DiophantineConsistency.Sign33ResidualAssembly

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualConverse05
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem residuals_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0))
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι (ports 1))
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι (ports 2))
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι (ports 3))
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    InternalZero (Sign33ResidualBatch05.tailResidual p 14) v ∧
    InternalZero (Sign33ResidualBatch05.tailResidual p 15) v ∧
    InternalZero (Sign33ResidualBatch05.tailResidual p 16) v := by
  have h15 : InternalZero (Sign33ResidualBatch05.tailResidual p 14) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch05.row15_eval p ports v hp0 hp1]
    exact sub_eq_zero.mpr hc.batch05.1
  have h16 : InternalZero (Sign33ResidualBatch05.tailResidual p 15) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch05.row16_eval p v]
    exact sub_eq_zero.mpr hc.batch05.2.1
  have h17 : InternalZero (Sign33ResidualBatch05.tailResidual p 16) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch05.row17_eval p ports v hp0 hp2 hp3]
    exact sub_eq_zero.mpr hc.batch05.2.2
  exact ⟨h15, h16, h17⟩
end DiophantineConsistency.Sign33ResidualConverse05
#print axioms DiophantineConsistency.Sign33ResidualConverse05.residuals_zero
