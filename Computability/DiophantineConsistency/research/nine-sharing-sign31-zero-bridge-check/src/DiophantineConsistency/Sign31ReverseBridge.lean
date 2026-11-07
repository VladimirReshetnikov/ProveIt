import DiophantineConsistency.Sign31ForwardBridge

/-! UNCOMPILED reverse seed-zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign31ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed31Sextic.firstResidual p :: SharingSeed31Sextic.remainingResiduals p =
      [SharingSeed31Sextic.firstResidual p,
       Sign31RemainingCuts.newX p,
       Sign31RemainingCuts.newY p,
       Sign31RemainingCuts.newE p,
       Sign31RemainingCuts.newkY p,
       Sign31RemainingCuts.newell p,
       Sign31RemainingCuts.newDelta p,
       Sign31RemainingCuts.newmainRoot p,
       Sign31RemainingCuts.newc2 p,
       Sign31RemainingCuts.newDc2 p,
       Sign31RemainingCuts.newN1 p,
       Sign31RemainingCuts.newgap p,
       Sign31RemainingCuts.newtau p,
       Sign31RemainingCuts.newN0 p,
       Sign31RemainingCuts.newNt p,
       Sign31RemainingCuts.newcTminusR p,
       Sign31FirstCut.newV p,
       Sign31RemainingCuts.newnormalizedS p,
       Sign31RemainingCuts.newnormalizedS2 p,
       Sign31RemainingCuts.newV2minusY2 p,
       Sign31RemainingCuts.newNa p,
       Sign31FirstCut.newscaledNs p] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 33 → V)
    (hz : InternalZero (SharingSeed32Sextic.seed p) v) :
    InternalZero (SharingSeed31Sextic.seed p) (Sign31CoordinateRecover.drop v) := by
  have hr := Sign31CoordinateRecover.lift_drop p v hz
  have hz' : InternalZero (SharingSeed32Sextic.seed p) (Sign31FirstCut.lift (Sign31CoordinateRecover.drop v)) := by
    rw [hr]
    exact hz
  have ho := (SharingSign32Squares.seed_zero_iff_residuals p (Sign31FirstCut.lift (Sign31CoordinateRecover.drop v))).mp hz'
  apply (SharingSign31Squares.seed_zero_iff_residuals p (Sign31CoordinateRecover.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.q3_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.X_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_X_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.Y_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_Y_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.E_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_E_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.kY_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_kY_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.ell_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_ell_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.Delta_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_Delta_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.mainRoot_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_mainRoot_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.c2_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_c2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.Dc2_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.N1_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_N1_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.gap_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_gap_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.tau_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.N0_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.Nt_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.cTminusR_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31FirstCut.V_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31FirstCut.old_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.normalizedS_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_normalizedS_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.normalizedS2_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_normalizedS2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.V2minusY2_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31RemainingCuts.Na_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31RemainingCuts.old_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign31FirstCut.scaledNs_eval p (Sign31CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign31FirstCut.old_scaledNs_row p)))))
end DiophantineConsistency.Sign31ZeroBridge
#print axioms DiophantineConsistency.Sign31ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign31ZeroBridge.backward
