import DiophantineConsistency.Sign27CoordinateDrop
import DiophantineConsistency.Sign27AffectedCuts

/-! SOURCE-ONLY: forward zero-set assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign27ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed28Sextic.firstResidual p :: SharingSeed28Sextic.remainingResiduals p =
      [SharingSeed28Sextic.firstResidual p,
       Sign27RemainingCuts.oldR01 p,
       Sign27RemainingCuts.oldR02 p,
       Sign27RemainingCuts.oldR03 p,
       Sign27RemainingCuts.oldR04 p,
       Sign27RemainingCuts.oldR05 p,
       Sign27AffectedCuts.oldMainRoot p,
       Sign27AffectedCuts.oldDc2 p,
       Sign27FirstCut.oldN1,
       Sign27RemainingCuts.oldR09 p,
       Sign27RemainingCuts.oldR10 p,
       Sign27RemainingCuts.oldR11 p,
       Sign27RemainingCuts.oldR12 p,
       Sign27RemainingCuts.oldR13 p,
       Sign27RemainingCuts.oldR14 p,
       Sign27AffectedCuts.oldNormalizedS p,
       Sign27RemainingCuts.oldR16 p,
       Sign27RemainingCuts.oldR17 p,
       Sign27RemainingCuts.oldR18 p] := by rfl

theorem forward (p : Fin 4 → ℤ) (v : Fin 28 → V)
    (hz : InternalZero (SharingSeed27Sextic.seed p) v) :
    InternalZero (SharingSeed28Sextic.seed p) (Sign27FirstCut.lift v) := by
  have hn := (SharingSign27Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign28Squares.seed_zero_iff_residuals p (Sign27FirstCut.lift v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27FirstCut.first_eval p v)).mpr (hn _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R01_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.new_R01_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R02_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.new_R02_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R03_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.new_R03_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R04_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.new_R04_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R05_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.new_R05_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27AffectedCuts.MainRoot_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27AffectedCuts.new_MainRoot_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27AffectedCuts.Dc2_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27AffectedCuts.new_Dc2_row p)))))
  · exact Sign27FirstCut.oldN1_zero v
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R09_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.new_R09_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R10_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.new_R10_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R11_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.new_R11_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R12_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.new_R12_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R13_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.new_R13_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R14_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.new_R14_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27AffectedCuts.NormalizedS_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27AffectedCuts.new_NormalizedS_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R16_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.new_R16_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R17_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.new_R17_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign27RemainingCuts.R18_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign27RemainingCuts.new_R18_row p)))))
end DiophantineConsistency.Sign27ZeroBridge
#print axioms DiophantineConsistency.Sign27ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign27ZeroBridge.forward
