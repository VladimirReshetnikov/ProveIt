import DiophantineConsistency.Sign25ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed25Octic.firstResidual p :: SharingSeed25Octic.remainingResiduals p =
      [SharingSeed25Octic.firstResidual p,
       Sign25RemainingCuts.newR01 p,
       Sign25RemainingCuts.newR02 p,
       Sign25RemainingCuts.newR03 p,
       Sign25RemainingCuts.newR05 p,
       Sign25RemainingCuts.newR06 p,
       Sign25RemainingCuts.newR07 p,
       Sign25RemainingCuts.newR08 p,
       Sign25FirstCut.newN0 p,
       Sign25RemainingCuts.newR10 p,
       Sign25RemainingCuts.newR11 p,
       Sign25RemainingCuts.newR12 p,
       Sign25RemainingCuts.newR13 p,
       Sign25RemainingCuts.newR14 p,
       Sign25RemainingCuts.newR15 p,
       Sign25RemainingCuts.newR16 p] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 27 → V)
    (hz : InternalZero (SharingSeed26Sextic.seed p) v) :
    InternalZero (SharingSeed25Octic.seed p) (Sign25CoordinateRecover.drop v) := by
  have hz' : InternalZero (SharingSeed26Sextic.seed p)
      (Sign25FirstCut.lift (Sign25CoordinateRecover.drop v)) := by
    rw [Sign25CoordinateRecover.lift_drop p v hz]
    exact hz
  have ho := (SharingSign26Squares.seed_zero_iff_residuals p
    (Sign25FirstCut.lift (Sign25CoordinateRecover.drop v))).mp hz'
  apply (SharingSign25Squares.seed_zero_iff_residuals p (Sign25CoordinateRecover.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.first_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R01_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.old_R01_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R02_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.old_R02_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R03_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.old_R03_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R05_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.old_R05_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R06_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.old_R06_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R07_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.old_R07_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R08_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.old_R08_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25FirstCut.N0_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25FirstCut.old_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R10_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.old_R10_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R11_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.old_R11_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R12_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.old_R12_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R13_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.old_R13_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R14_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.old_R14_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R15_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.old_R15_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R16_eval p (Sign25CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.old_R16_row p)))))
end DiophantineConsistency.Sign25ZeroBridge
#print axioms DiophantineConsistency.Sign25ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign25ZeroBridge.backward
