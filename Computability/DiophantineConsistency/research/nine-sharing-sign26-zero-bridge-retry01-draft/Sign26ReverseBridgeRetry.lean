import DiophantineConsistency.Sign26ReverseGap

/-! SOURCE-ONLY: reverse zero assembly; q3 and old gap extracted from old zero. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed26Sextic.firstResidual p :: SharingSeed26Sextic.remainingResiduals p =
      [SharingSeed26Sextic.firstResidual p,
       Sign26RemainingCuts.newR01 p,
       Sign26RemainingCuts.newR02 p,
       Sign26RemainingCuts.newR03 p,
       Sign26RemainingCuts.newR04 p,
       Sign26RemainingCuts.newR05 p,
       Sign26RemainingCuts.newR06 p,
       Sign26RemainingCuts.newR07 p,
       Sign26CongruenceCuts.newTau p,
       Sign26RemainingCuts.newR10 p,
       Sign26RemainingCuts.newR11 p,
       Sign26CongruenceCuts.newInner p,
       Sign26RemainingCuts.newR13 p,
       Sign26RemainingCuts.newR14 p,
       Sign26RemainingCuts.newR15 p,
       Sign26RemainingCuts.newR16 p,
       Sign26RemainingCuts.newR17 p] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 28 → V)
    (hz : InternalZero (SharingSeed27Sextic.seed p) v) :
    InternalZero (SharingSeed26Sextic.seed p) (drop v) := by
  have hr := lift_drop v
  have hz' : InternalZero (SharingSeed27Sextic.seed p) (Sign26CongruenceCuts.lift (v 22) (drop v)) := by
    rw [hr]
    exact hz
  have ho := (SharingSign27Squares.seed_zero_iff_residuals p (Sign26CongruenceCuts.lift (v 22) (drop v))).mp hz'
  have hfirst : InternalZero (SharingSeed26Sextic.firstResidual p) (drop v) :=
    (zero_iff_of_eval_eq _ _ _ _ (Sign26CongruenceCuts.first_eval p (drop v) (v 22))).mp (ho _ List.mem_cons_self)
  have hq3 := (internalZero_iff _ _).mp hfirst
  simp only [SharingSeed26Sextic.firstResidual, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] at hq3
  have hq3 := sub_eq_zero.mp hq3
  have hgold := ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26CongruenceCuts.old_Gap_row p))))
  have hgap : ι (v 22) = Sign26CongruenceCuts.ringGap p (drop v) :=
    reverseGap p (drop v) (v 22) hgold
  apply (SharingSign26Squares.seed_zero_iff_residuals p (drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hfirst
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R01_eval p (drop v) (v 22))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.old_R01_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R02_eval p (drop v) (v 22))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.old_R02_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R03_eval p (drop v) (v 22))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.old_R03_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R04_eval p (drop v) (v 22))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.old_R04_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R05_eval p (drop v) (v 22))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.old_R05_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R06_eval p (drop v) (v 22))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.old_R06_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R07_eval p (drop v) (v 22))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.old_R07_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26CongruenceCuts.Tau_eval p (drop v) (v 22) hgap hq3)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26CongruenceCuts.old_Tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R10_eval p (drop v) (v 22))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.old_R10_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R11_eval p (drop v) (v 22))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.old_R11_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26CongruenceCuts.Inner_eval p (drop v) (v 22) hgap hq3)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26CongruenceCuts.old_Inner_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R13_eval p (drop v) (v 22))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.old_R13_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R14_eval p (drop v) (v 22))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.old_R14_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R15_eval p (drop v) (v 22))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.old_R15_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R16_eval p (drop v) (v 22))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.old_R16_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign26RemainingCuts.R17_eval p (drop v) (v 22))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign26RemainingCuts.old_R17_row p)))))
end DiophantineConsistency.Sign26ZeroBridge
#print axioms DiophantineConsistency.Sign26ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign26ZeroBridge.backward
