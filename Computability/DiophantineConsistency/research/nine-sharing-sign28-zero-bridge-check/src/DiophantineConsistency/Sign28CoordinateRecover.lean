import DiophantineConsistency.Sign28RemainingCuts01

/-! UNCOMPILED: recover the three eliminated sign31 natural coordinates. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28CoordinateRecover
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem x_coordinate (p : Fin 4 → ℤ) (beta : V) (v : Fin 32 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed31Sextic.seed p) v) :
    v 16 = (v 9 + 1) * (beta * (v 1 + 1) + 1) := by
  have hm : Sign28FirstCuts.oldX p ∈ SharingSeed31Sextic.firstResidual p :: SharingSeed31Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28FirstCuts.old_X_row p)))
  have he := (internalZero_iff _ _).mp ((SharingSign31Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [Sign28FirstCuts.oldX, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, hp0] at he
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  exact sub_eq_zero.mp he

theorem c2_coordinate (p : Fin 4 → ℤ) (v : Fin 32 → V)
    (hz : InternalZero (SharingSeed31Sextic.seed p) v) :
    v 23 = (v 19 + (v 11 + 1)) ^ 2 := by
  have hm : Sign28FirstCuts.oldc2 p ∈ SharingSeed31Sextic.firstResidual p :: SharingSeed31Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28FirstCuts.old_c2_row p)))
  have he := (internalZero_iff _ _).mp ((SharingSign31Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [Sign28FirstCuts.oldc2, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] at he
  apply ι_injective
  simp only [pow_two, map_add, map_mul, map_one]
  exact sub_eq_zero.mp he

theorem s2_coordinate (p : Fin 4 → ℤ) (v : Fin 32 → V)
    (hz : InternalZero (SharingSeed31Sextic.seed p) v) :
    v 30 = (v 29) ^ 2 := by
  have hm : Sign28FirstCuts.oldnormalizedS2 p ∈ SharingSeed31Sextic.firstResidual p :: SharingSeed31Sextic.remainingResiduals p :=
    List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28FirstCuts.old_normalizedS2_row p)))
  have he := (internalZero_iff _ _).mp ((SharingSign31Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [Sign28FirstCuts.oldnormalizedS2, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var] at he
  apply ι_injective
  simp only [pow_two, map_mul]
  exact sub_eq_zero.mp he
end DiophantineConsistency.Sign28CoordinateRecover
#print axioms DiophantineConsistency.Sign28CoordinateRecover.x_coordinate
#print axioms DiophantineConsistency.Sign28CoordinateRecover.c2_coordinate
#print axioms DiophantineConsistency.Sign28CoordinateRecover.s2_coordinate
