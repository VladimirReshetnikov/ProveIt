import DiophantineConsistency.Sign33ResidualAssembly

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualConverse03
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
    InternalZero (Sign33ResidualBatch03.tailResidual p 8) v ∧
    InternalZero (Sign33ResidualBatch03.tailResidual p 9) v ∧
    InternalZero (Sign33ResidualBatch03.tailResidual p 10) v := by
  have h9 : InternalZero (Sign33ResidualBatch03.tailResidual p 8) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch03.row9_eval p v]
    exact sub_eq_zero.mpr hc.batch03.1
  have h10 : InternalZero (Sign33ResidualBatch03.tailResidual p 9) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch03.row10_eval p v]
    exact sub_eq_zero.mpr hc.batch03.2.1
  have h11 : InternalZero (Sign33ResidualBatch03.tailResidual p 10) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch03.row11_eval p v]
    exact sub_eq_zero.mpr hc.batch03.2.2
  exact ⟨h9, h10, h11⟩
end DiophantineConsistency.Sign33ResidualConverse03
#print axioms DiophantineConsistency.Sign33ResidualConverse03.residuals_zero
