import DiophantineConsistency.Sign25RemainingCuts01

/-! SOURCE-ONLY: recover the deleted product coordinate from an old zero. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25CoordinateRecover
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ell_coordinate (p : Fin 4 → ℤ) (v : Fin 27 → V)
    (hz : InternalZero (SharingSeed26Sextic.seed p) v) :
    v 19 = v 17 * v 18 := by
  have hm : Sign25FirstCut.oldEll p ∈ SharingSeed26Sextic.firstResidual p :: SharingSeed26Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25FirstCut.old_ell_row p)))
  have he := (internalZero_iff _ _).mp ((SharingSign26Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [Sign25FirstCut.oldEll, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var] at he
  apply ι_injective
  rw [map_mul]
  exact sub_eq_zero.mp he
end DiophantineConsistency.Sign25CoordinateRecover
#print axioms DiophantineConsistency.Sign25CoordinateRecover.ell_coordinate
