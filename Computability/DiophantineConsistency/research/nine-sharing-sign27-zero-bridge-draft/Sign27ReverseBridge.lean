import DiophantineConsistency.Sign27ForwardBridge
import DiophantineConsistency.Sign27SeedRootRecovery

/-! SOURCE-ONLY: reverse zero-set assembly with an explicit predecessor. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign27ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed27Sextic.firstResidual p :: SharingSeed27Sextic.remainingResiduals p =
      [SharingSeed27Sextic.firstResidual p,
       Sign27RemainingCuts.newR01 p,
       Sign27RemainingCuts.newR02 p,
       Sign27RemainingCuts.newR03 p,
       Sign27RemainingCuts.newR04 p,
       Sign27RemainingCuts.newR05 p,
       Sign27AffectedCuts.newMainRoot p,
       Sign27AffectedCuts.newDc2 p,
       Sign27RemainingCuts.newR09 p,
       Sign27RemainingCuts.newR10 p,
       Sign27RemainingCuts.newR11 p,
       Sign27RemainingCuts.newR12 p,
       Sign27RemainingCuts.newR13 p,
       Sign27RemainingCuts.newR14 p,
       Sign27AffectedCuts.newNormalizedS p,
       Sign27RemainingCuts.newR16 p,
       Sign27RemainingCuts.newR17 p,
       Sign27RemainingCuts.newR18 p] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 29 → V)
    (hz : InternalZero (SharingSeed28Sextic.seed p) v) :
    ∃ u : V, v 21 = u + 1 ∧ v 22 = u * (u + 2) ∧
      InternalZero (SharingSeed27Sextic.seed p) (drop u v) := by
  obtain ⟨u, hx, hy⟩ := Sign27SeedRootRecovery.recover p v hz
  refine ⟨u, hx, hy, ?_⟩
  have hr := lift_drop v u hx hy
  have hz' : InternalZero (SharingSeed28Sextic.seed p) (Sign27FirstCut.lift (drop u v)) := by
    rw [hr]
    exact hz
  have ho := (SharingSign28Squares.seed_zero_iff_residuals p (Sign27FirstCut.lift (drop u v))).mp hz'
  apply (SharingSign27Squares.seed_zero_iff_residuals p (drop u v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27FirstCut.first_eval p (drop u v))).mp (ho _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R01_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.old_R01_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R02_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.old_R02_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R03_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.old_R03_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R04_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.old_R04_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R05_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.old_R05_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27AffectedCuts.MainRoot_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27AffectedCuts.old_MainRoot_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27AffectedCuts.Dc2_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27AffectedCuts.old_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R09_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.old_R09_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R10_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.old_R10_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R11_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.old_R11_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R12_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.old_R12_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R13_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.old_R13_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R14_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.old_R14_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27AffectedCuts.NormalizedS_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27AffectedCuts.old_NormalizedS_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R16_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.old_R16_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R17_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.old_R17_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R18_eval p (drop u v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.old_R18_row p)))))
end DiophantineConsistency.Sign27ZeroBridge
#print axioms DiophantineConsistency.Sign27ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign27ZeroBridge.backward
