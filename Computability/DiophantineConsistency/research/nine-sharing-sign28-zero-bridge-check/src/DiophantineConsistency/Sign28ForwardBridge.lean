import DiophantineConsistency.Sign28CoordinateDrop

/-! UNCOMPILED forward seed-zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed31Sextic.firstResidual p :: SharingSeed31Sextic.remainingResiduals p =
      [SharingSeed31Sextic.firstResidual p,
       Sign28FirstCuts.oldX p,
       Sign28RemainingCuts.oldY p,
       Sign28FirstCuts.oldE p,
       Sign28RemainingCuts.oldkY p,
       Sign28RemainingCuts.oldell p,
       Sign28RemainingCuts.oldDelta p,
       Sign28FirstCuts.oldmainRoot p,
       Sign28FirstCuts.oldc2 p,
       Sign28FirstCuts.oldDc2 p,
       Sign28RemainingCuts.oldN1 p,
       Sign28RemainingCuts.oldgap p,
       Sign28RemainingCuts.oldtau p,
       Sign28RemainingCuts.oldN0 p,
       Sign28RemainingCuts.oldNt p,
       Sign28RemainingCuts.oldcTminusR p,
       Sign28RemainingCuts.oldV p,
       Sign28RemainingCuts.oldnormalizedS p,
       Sign28FirstCuts.oldnormalizedS2 p,
       Sign28RemainingCuts.oldV2minusY2 p,
       Sign28FirstCuts.oldNa p,
       Sign28FirstCuts.oldscaledNs p] := by rfl

theorem forward (p : Fin 4 → ℤ) (beta : V) (v : Fin 29 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed28Sextic.seed p) v) :
    InternalZero (SharingSeed31Sextic.seed p) (Sign28FirstCuts.lift beta v) := by
  have hn := (SharingSign28Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign31Squares.seed_zero_iff_residuals p (Sign28FirstCuts.lift beta v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.q3_eval p beta v)).mpr (hn _ List.mem_cons_self)
  · exact Sign28FirstCuts.old_X_zero p beta v hp0
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.Y_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.new_Y_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28FirstCuts.E_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28FirstCuts.new_E_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.kY_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.new_kY_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.ell_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.new_ell_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.Delta_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.new_Delta_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28FirstCuts.mainRoot_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28FirstCuts.new_mainRoot_row p)))))
  · exact Sign28FirstCuts.old_c2_zero p beta v
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28FirstCuts.Dc2_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28FirstCuts.new_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.N1_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.new_N1_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.gap_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.new_gap_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.tau_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.new_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.N0_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.new_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.Nt_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.new_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.cTminusR_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.new_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.V_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.new_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.normalizedS_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.new_normalizedS_row p)))))
  · exact Sign28FirstCuts.old_normalizedS2_zero p beta v
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.V2minusY2_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.new_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28FirstCuts.Na_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28FirstCuts.new_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28FirstCuts.scaledNs_eval p beta v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28FirstCuts.new_scaledNs_row p)))))
end DiophantineConsistency.Sign28ZeroBridge
#print axioms DiophantineConsistency.Sign28ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign28ZeroBridge.forward
