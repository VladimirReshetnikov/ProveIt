import DiophantineConsistency.Sign33ResidualAssembly

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ResidualConverse00
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
    InternalZero (SharingSeed33.firstResidual p) v ∧
    InternalZero (Sign33ResidualBatch00.tailResidual p 0) v ∧
    InternalZero (Sign33ResidualBatch00.tailResidual p 1) v := by
  have h0 : InternalZero (SharingSeed33.firstResidual p) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33FirstCut.first_residual_eval p ports v hp0]
    apply sub_eq_zero.mpr
    simpa only [Sign33ResidualBatch00.q] using hc.batch00.1
  have h1 : InternalZero (Sign33ResidualBatch00.tailResidual p 0) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch00.row1_eval p ports v hp0]
    exact sub_eq_zero.mpr hc.batch00.2.1
  have h2 : InternalZero (Sign33ResidualBatch00.tailResidual p 1) v := by
    apply (internalZero_iff _ v).mpr
    rw [Sign33ResidualBatch00.row2_eval p ports v hp0]
    exact sub_eq_zero.mpr hc.batch00.2.2
  exact ⟨h0, h1, h2⟩
end DiophantineConsistency.Sign33ResidualConverse00
#print axioms DiophantineConsistency.Sign33ResidualConverse00.residuals_zero
