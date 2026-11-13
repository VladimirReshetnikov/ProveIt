import DiophantineConsistency.Sign14SharedValues

/-! SOURCE-ONLY extraction of natural transport equation from retained Nt. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14TransportRow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingSeed14Degree124 Sign14SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem transport_of_seed (p : Fin 4 → ℤ) (beta K : V) (v : Fin 15 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι K)
    (hz : InternalZero (SharingSeed14Degree124.seed p) v) :
    (K + (v 9 + 1)) * A beta v + A beta v =
      (K + (v 9 + 1)) * ((v 2 + 1) + (v 3 + 1)) + (v 2 + 1) +
        (v 4 + 1) * (A beta v - 1) + 1 := by
  have hm : row02 p ∈ firstResidual p :: remainingResiduals p := by
    simp [firstResidual, remainingResiduals]
  have he := (internalZero_iff _ _).mp ((SharingSign14Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [row02, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, hp0, hp1, Int.cast_one] at he
  have hq : A beta v - 1 = beta * (v 1 + 1) := by simp [A]
  rw [hq]
  apply ι_injective
  simp only [A, map_add, map_mul, map_one]
  linarith only [he]
end DiophantineConsistency.Sign14TransportRow
#print axioms DiophantineConsistency.Sign14TransportRow.transport_of_seed
