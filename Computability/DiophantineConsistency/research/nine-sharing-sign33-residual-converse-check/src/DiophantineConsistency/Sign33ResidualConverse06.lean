import DiophantineConsistency.Sign33ResidualAssembly

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualConverse06
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
    InternalZero (Sign33ResidualBatch06.tailResidual p 17) v ∧
    InternalZero (Sign33ResidualBatch06.tailResidual p 18) v ∧
    InternalZero (Sign33ResidualBatch06.tailResidual p 19) v := by
  have h18 : InternalZero (Sign33ResidualBatch06.tailResidual p 17) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch06.row18_eval p v]
    exact sub_eq_zero.mpr hc.batch06.1
  have h19 : InternalZero (Sign33ResidualBatch06.tailResidual p 18) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch06.row19_eval p v]
    exact sub_eq_zero.mpr hc.batch06.2.1
  have h20 : InternalZero (Sign33ResidualBatch06.tailResidual p 19) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch06.row20_eval p v]
    exact sub_eq_zero.mpr hc.batch06.2.2
  exact ⟨h18, h19, h20⟩
end DiophantineConsistency.Sign33ResidualConverse06
#print axioms DiophantineConsistency.Sign33ResidualConverse06.residuals_zero
