import DiophantineConsistency.Sign32Substitution07

/-! UNCOMPILED: recover the eliminated natural q² coordinate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32CoordinateRecover
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem q2_coordinate (p : Fin 4 → ℤ) (beta : V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed33.seed p) v) :
    v 15 = (beta * (v 1 + 1) + 1) ^ 2 := by
  have hres : InternalZero (SharingSeed33.firstResidual p) v :=
    (SharingSign33Squares.seed_zero_iff_residuals p v).mp hz _ List.mem_cons_self
  have he := (internalZero_iff _ _).mp hres
  simp only [SharingSeed33.firstResidual, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, hp0] at he
  apply ι_injective
  simp only [pow_two, map_add, map_mul, map_one]
  exact sub_eq_zero.mp he
end DiophantineConsistency.Sign32CoordinateRecover
#print axioms DiophantineConsistency.Sign32CoordinateRecover.q2_coordinate
