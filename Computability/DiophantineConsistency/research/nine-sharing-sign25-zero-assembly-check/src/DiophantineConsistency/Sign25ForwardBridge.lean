import DiophantineConsistency.Sign25CoordinateDrop

/-! SOURCE-ONLY forward zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed26Sextic.firstResidual p :: SharingSeed26Sextic.remainingResiduals p =
      [SharingSeed26Sextic.firstResidual p,
       Sign25RemainingCuts.oldR01 p,
       Sign25RemainingCuts.oldR02 p,
       Sign25RemainingCuts.oldR03 p,
       Sign25FirstCut.oldEll p,
       Sign25RemainingCuts.oldR05 p,
       Sign25RemainingCuts.oldR06 p,
       Sign25RemainingCuts.oldR07 p,
       Sign25RemainingCuts.oldR08 p,
       Sign25FirstCut.oldN0 p,
       Sign25RemainingCuts.oldR10 p,
       Sign25RemainingCuts.oldR11 p,
       Sign25RemainingCuts.oldR12 p,
       Sign25RemainingCuts.oldR13 p,
       Sign25RemainingCuts.oldR14 p,
       Sign25RemainingCuts.oldR15 p,
       Sign25RemainingCuts.oldR16 p] := by rfl

theorem forward (p : Fin 4 → ℤ) (v : Fin 26 → V)
    (hz : InternalZero (SharingSeed25Octic.seed p) v) :
    InternalZero (SharingSeed26Sextic.seed p) (Sign25FirstCut.lift v) := by
  have hn := (SharingSign25Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign26Squares.seed_zero_iff_residuals p (Sign25FirstCut.lift v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.first_eval p v)).mpr (hn _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R01_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.new_R01_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R02_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.new_R02_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R03_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.new_R03_row p)))))
  · exact Sign25FirstCut.old_ell_zero p v
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R05_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.new_R05_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R06_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.new_R06_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R07_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.new_R07_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R08_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.new_R08_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25FirstCut.N0_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25FirstCut.new_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R10_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.new_R10_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R11_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.new_R11_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R12_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.new_R12_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R13_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.new_R13_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R14_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.new_R14_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R15_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.new_R15_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign25RemainingCuts.R16_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign25RemainingCuts.new_R16_row p)))))
end DiophantineConsistency.Sign25ZeroBridge
#print axioms DiophantineConsistency.Sign25ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign25ZeroBridge.forward
