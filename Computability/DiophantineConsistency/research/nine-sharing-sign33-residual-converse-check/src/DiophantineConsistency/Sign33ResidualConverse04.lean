import DiophantineConsistency.Sign33ResidualAssembly

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualConverse04
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
    InternalZero (Sign33ResidualBatch04.tailResidual p 11) v ∧
    InternalZero (Sign33ResidualBatch04.tailResidual p 12) v ∧
    InternalZero (Sign33ResidualBatch04.tailResidual p 13) v := by
  have h12 : InternalZero (Sign33ResidualBatch04.tailResidual p 11) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch04.row12_eval p ports v hp0]
    exact sub_eq_zero.mpr hc.batch04.1
  have h13 : InternalZero (Sign33ResidualBatch04.tailResidual p 12) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch04.row13_eval p ports v hp0 hp2 hp3]
    exact sub_eq_zero.mpr hc.batch04.2.1
  have h14 : InternalZero (Sign33ResidualBatch04.tailResidual p 13) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch04.row14_eval p v]
    exact sub_eq_zero.mpr hc.batch04.2.2
  exact ⟨h12, h13, h14⟩
end DiophantineConsistency.Sign33ResidualConverse04
#print axioms DiophantineConsistency.Sign33ResidualConverse04.residuals_zero
