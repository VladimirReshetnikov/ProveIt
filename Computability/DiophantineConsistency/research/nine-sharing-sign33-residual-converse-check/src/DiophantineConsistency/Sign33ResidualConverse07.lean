import DiophantineConsistency.Sign33ResidualAssembly

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualConverse07
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
    InternalZero (Sign33ResidualBatch07.tailResidual p 20) v ∧
    InternalZero (Sign33ResidualBatch07.tailResidual p 21) v ∧
    InternalZero (Sign33ResidualBatch07.tailResidual p 22) v := by
  have h21 : InternalZero (Sign33ResidualBatch07.tailResidual p 20) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch07.row21_eval p v]
    exact sub_eq_zero.mpr hc.batch07.1
  have h22 : InternalZero (Sign33ResidualBatch07.tailResidual p 21) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch07.row22_eval p v]
    exact sub_eq_zero.mpr hc.batch07.2.1
  have h23 : InternalZero (Sign33ResidualBatch07.tailResidual p 22) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch07.row23_eval p v]
    exact sub_eq_zero.mpr hc.batch07.2.2
  exact ⟨h21, h22, h23⟩
end DiophantineConsistency.Sign33ResidualConverse07
#print axioms DiophantineConsistency.Sign33ResidualConverse07.residuals_zero
