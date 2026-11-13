import DiophantineConsistency.SharingSign33Squares

/-! Bind the first sign33 residual to its q-square static cut. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33FirstCut
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_residual_eval (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0)) :
    (SharingSeed33.firstResidual p).evalRing (fun j => ι (v j)) =
      ι (v 15) - (ι (ports 0)*(ι (v 1)+1)+1)*(ι (ports 0)*(ι (v 1)+1)+1) := by
  simp only [SharingSeed33.firstResidual, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one, hp0]

theorem first_cut_of_seed_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0))
    (hz : InternalZero (SharingSeed33.seed p) v) :
    ι (v 15) = (ι (ports 0)*(ι (v 1)+1)+1)*(ι (ports 0)*(ι (v 1)+1)+1) := by
  have hres : InternalZero (SharingSeed33.firstResidual p) v :=
    (SharingSign33Squares.seed_zero_iff_residuals p v).mp hz _ (List.mem_cons_self)
  have he := (internalZero_iff (SharingSeed33.firstResidual p) v).mp hres
  rw [first_residual_eval p ports v hp0] at he
  exact sub_eq_zero.mp he
end DiophantineConsistency.Sign33FirstCut
#print axioms DiophantineConsistency.Sign33FirstCut.first_residual_eval
#print axioms DiophantineConsistency.Sign33FirstCut.first_cut_of_seed_zero
