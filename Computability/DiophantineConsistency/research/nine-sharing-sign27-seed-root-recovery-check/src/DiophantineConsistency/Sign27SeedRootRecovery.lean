import DiophantineConsistency.Sign27RootRecovery

/-! SOURCE-ONLY: extract the old N1 equation and use abstract root recovery. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign27SeedRootRecovery
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def oldN1 : Expr (Fin 29) :=
  (Expr.var 21 * Expr.var 21 - Expr.var 22) - Expr.constant (1 : ℤ)

theorem oldN1_row (p : Fin 4 → ℤ) :
    oldN1 ∈ SharingSeed28Sextic.firstResidual p :: SharingSeed28Sextic.remainingResiduals p := by
  simp [SharingSeed28Sextic.remainingResiduals, oldN1]

theorem recover (p : Fin 4 → ℤ) (v : Fin 29 → V)
    (hz : InternalZero (SharingSeed28Sextic.seed p) v) :
    ∃ u : V, v 21 = u + 1 ∧ v 22 = u * (u + 2) := by
  have hzN := (SharingSign28Squares.seed_zero_iff_residuals p v).mp hz oldN1 (oldN1_row p)
  have he := (internalZero_iff _ _).mp hzN
  simp only [oldN1, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] at he
  have hnorm : ι (v 21) * ι (v 21) = ι (v 22) + 1 := by
    have h := (sub_eq_iff_eq_add).mp (sub_eq_zero.mp he)
    simpa only [add_comm] using h
  exact Sign27RootRecovery.recover (v 21) (v 22) hnorm
end DiophantineConsistency.Sign27SeedRootRecovery
#print axioms DiophantineConsistency.Sign27SeedRootRecovery.oldN1_row
#print axioms DiophantineConsistency.Sign27SeedRootRecovery.recover
