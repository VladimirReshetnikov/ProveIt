import DiophantineConsistency.Sign33ResidualAssembly

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualConverse01
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
    InternalZero (Sign33ResidualBatch01.tailResidual p 2) v ∧
    InternalZero (Sign33ResidualBatch01.tailResidual p 3) v ∧
    InternalZero (Sign33ResidualBatch01.tailResidual p 4) v := by
  have h3 : InternalZero (Sign33ResidualBatch01.tailResidual p 2) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch01.row3_eval p v]
    exact sub_eq_zero.mpr hc.batch01.1
  have h4 : InternalZero (Sign33ResidualBatch01.tailResidual p 3) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch01.row4_eval p v]
    exact sub_eq_zero.mpr hc.batch01.2.1
  have h5 : InternalZero (Sign33ResidualBatch01.tailResidual p 4) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch01.row5_eval p v]
    exact sub_eq_zero.mpr hc.batch01.2.2
  exact ⟨h3, h4, h5⟩
end DiophantineConsistency.Sign33ResidualConverse01
#print axioms DiophantineConsistency.Sign33ResidualConverse01.residuals_zero
