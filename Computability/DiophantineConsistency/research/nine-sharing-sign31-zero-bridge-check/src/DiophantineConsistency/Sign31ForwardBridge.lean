import DiophantineConsistency.Sign31CoordinateDrop

/-! UNCOMPILED forward seed-zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign31ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed32Sextic.firstResidual p :: SharingSeed32Sextic.remainingResiduals p =
      [SharingSeed32Sextic.firstResidual p,
       Sign31RemainingCuts.oldX p,
       Sign31RemainingCuts.oldY p,
       Sign31RemainingCuts.oldE p,
       Sign31RemainingCuts.oldkY p,
       Sign31RemainingCuts.oldell p,
       Sign31RemainingCuts.oldDelta p,
       Sign31RemainingCuts.oldmainRoot p,
       Sign31RemainingCuts.oldc2 p,
       Sign31RemainingCuts.oldDc2 p,
       Sign31RemainingCuts.oldN1 p,
       Sign31RemainingCuts.oldgap p,
       Sign31RemainingCuts.oldtau p,
       Sign31RemainingCuts.oldN0 p,
       Sign31RemainingCuts.oldNt p,
       Sign31FirstCut.oldF2 p,
       Sign31RemainingCuts.oldcTminusR p,
       Sign31FirstCut.oldV p,
       Sign31RemainingCuts.oldnormalizedS p,
       Sign31RemainingCuts.oldnormalizedS2 p,
       Sign31RemainingCuts.oldV2minusY2 p,
       Sign31RemainingCuts.oldNa p,
       Sign31FirstCut.oldscaledNs p] := by rfl

theorem forward (p : Fin 4 → ℤ) (v : Fin 32 → V)
    (hz : InternalZero (SharingSeed31Sextic.seed p) v) :
    InternalZero (SharingSeed32Sextic.seed p) (Sign31FirstCut.lift v) := by
  have hn := (SharingSign31Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign32Squares.seed_zero_iff_residuals p (Sign31FirstCut.lift v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.q3_eval p v)).mpr (hn _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.X_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_X_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.Y_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_Y_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.E_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_E_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.kY_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_kY_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.ell_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_ell_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.Delta_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_Delta_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.mainRoot_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_mainRoot_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.c2_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_c2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.Dc2_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.N1_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_N1_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.gap_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_gap_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.tau_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.N0_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.Nt_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_Nt_row p)))))
  · exact Sign31FirstCut.old_f2_zero p v
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.cTminusR_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31FirstCut.V_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31FirstCut.new_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.normalizedS_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_normalizedS_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.normalizedS2_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_normalizedS2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.V2minusY2_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.Na_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.new_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31FirstCut.scaledNs_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31FirstCut.new_scaledNs_row p)))))
end DiophantineConsistency.Sign31ZeroBridge
#print axioms DiophantineConsistency.Sign31ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign31ZeroBridge.forward
