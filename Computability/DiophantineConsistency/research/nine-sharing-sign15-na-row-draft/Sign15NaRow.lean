import DiophantineConsistency.SharingSign15Squares

/-! SOURCE-ONLY extraction of the signed Na row with abstract shared values. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign15NaRow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def E (p : Fin 4 → ℤ) (v : Fin 16 → V) (e : Expr (Fin 16)) : DiffRing V :=
  e.evalRing (fun j => ι (v j))

theorem signed_na_of_seed (p : Fin 4 → ℤ) (v : Fin 16 → V)
    (hz : InternalZero (SharingSeed15Degree124.seed p) v) :
    (ι (v 13) + 1) * (ι (v 13) + 1) -
      (E p v (SharingSeed15Degree124.shared38 p) * E p v (SharingSeed15Degree124.shared38 p)) *
        ((ι (v 13) + 1) * (ι (v 13) + 1) -
          E p v (SharingSeed15Degree124.shared33 p) * E p v (SharingSeed15Degree124.shared33 p)) - 1 = 0 := by
  have hm : SharingSeed15Degree124.row04 p ∈
      SharingSeed15Degree124.firstResidual p :: SharingSeed15Degree124.remainingResiduals p := by
    simp [SharingSeed15Degree124.firstResidual, SharingSeed15Degree124.remainingResiduals]
  have he := (internalZero_iff _ _).mp ((SharingSign15Squares.seed_zero_iff_residuals p v).mp hz _ hm)
  simp only [SharingSeed15Degree124.row04, SharingSeed15Degree124.shared39,
    Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var,
    Expr.evalRing_constant, Int.cast_one] at he
  exact he
end DiophantineConsistency.Sign15NaRow
#print axioms DiophantineConsistency.Sign15NaRow.signed_na_of_seed
