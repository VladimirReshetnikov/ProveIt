import DiophantineConsistency.Sign31RemainingCuts01

/-! UNCOMPILED: recover old f² coordinate from sign32 zero. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign31CoordinateRecover
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem f2_coordinate (p : Fin 4 → ℤ) (v : Fin 33 → V)
    (hz : InternalZero (SharingSeed32Sextic.seed p) v) :
    v 27 = (v 5 + 1) ^ 2 := by
  have hm : Sign31FirstCut.oldF2 p ∈ SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31FirstCut.old_f2_row p)))
  have he := (internalZero_iff _ _).mp ((SharingSign32Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [Sign31FirstCut.oldF2, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] at he
  apply ι_injective
  simp only [pow_two, map_add, map_mul, map_one]
  exact sub_eq_zero.mp he
end DiophantineConsistency.Sign31CoordinateRecover
#print axioms DiophantineConsistency.Sign31CoordinateRecover.f2_coordinate
