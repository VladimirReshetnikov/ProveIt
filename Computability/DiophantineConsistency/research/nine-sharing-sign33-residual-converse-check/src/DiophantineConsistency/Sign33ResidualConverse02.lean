import DiophantineConsistency.Sign33ResidualAssembly

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualConverse02
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
    InternalZero (Sign33ResidualBatch02.tailResidual p 5) v ∧
    InternalZero (Sign33ResidualBatch02.tailResidual p 6) v ∧
    InternalZero (Sign33ResidualBatch02.tailResidual p 7) v := by
  have h6 : InternalZero (Sign33ResidualBatch02.tailResidual p 5) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch02.row6_eval p v]
    exact sub_eq_zero.mpr hc.batch02.1
  have h7 : InternalZero (Sign33ResidualBatch02.tailResidual p 6) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch02.row7_eval p v]
    exact sub_eq_zero.mpr hc.batch02.2.1
  have h8 : InternalZero (Sign33ResidualBatch02.tailResidual p 7) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch02.row8_eval p v]
    exact sub_eq_zero.mpr hc.batch02.2.2
  exact ⟨h6, h7, h8⟩
end DiophantineConsistency.Sign33ResidualConverse02
#print axioms DiophantineConsistency.Sign33ResidualConverse02.residuals_zero
