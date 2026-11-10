import DiophantineConsistency.SharingSign16Squares

/-! SOURCE-ONLY extraction of two signed row consequences; no sign conclusion. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16RowPremises
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def E (p : Fin 4 → ℤ) (v : Fin 17 → V) (e : Expr (Fin 17)) : DiffRing V :=
  e.evalRing (fun j => ι (v j))

theorem inner_of_seed (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (hz : InternalZero (SharingSeed16Degree112.seed p) v) :
    ι (v 16) = E p v (SharingSeed16Degree112.shared18 p) * (ι (v 7) + 1) +
      E p v (SharingSeed16Degree112.shared15 p) - E p v (SharingSeed16Degree112.shared25 p) := by
  have hm : SharingSeed16Degree112.row04 p ∈
      SharingSeed16Degree112.firstResidual p :: SharingSeed16Degree112.remainingResiduals p := by
    simp [SharingSeed16Degree112.firstResidual, SharingSeed16Degree112.remainingResiduals]
  have he := (internalZero_iff _ _).mp ((SharingSign16Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [SharingSeed16Degree112.row04, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] at he
  exact sub_eq_zero.mp he

theorem signed_na_of_seed (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (hz : InternalZero (SharingSeed16Degree112.seed p) v) :
    (ι (v 13) + 1) * (ι (v 13) + 1) -
      (E p v (SharingSeed16Degree112.shared35 p) * E p v (SharingSeed16Degree112.shared35 p)) *
        ((ι (v 13) + 1) * (ι (v 13) + 1) -
          (((ι (v 5) + 1) * (ι (v 5) + 1) * ι (v 16)) - E p v (SharingSeed16Degree112.shared18 p)) *
          (((ι (v 5) + 1) * (ι (v 5) + 1) * ι (v 16)) - E p v (SharingSeed16Degree112.shared18 p))) - 1 = 0 := by
  have hm : SharingSeed16Degree112.row05 p ∈
      SharingSeed16Degree112.firstResidual p :: SharingSeed16Degree112.remainingResiduals p := by
    simp [SharingSeed16Degree112.firstResidual, SharingSeed16Degree112.remainingResiduals]
  have he := (internalZero_iff _ _).mp ((SharingSign16Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [SharingSeed16Degree112.row05, SharingSeed16Degree112.shared36,
    SharingSeed16Degree112.shared20, SharingSeed16Degree112.shared01,
    Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var,
    Expr.evalRing_constant, Int.cast_one] at he
  exact he
end DiophantineConsistency.Sign16RowPremises
#print axioms DiophantineConsistency.Sign16RowPremises.inner_of_seed
#print axioms DiophantineConsistency.Sign16RowPremises.signed_na_of_seed
