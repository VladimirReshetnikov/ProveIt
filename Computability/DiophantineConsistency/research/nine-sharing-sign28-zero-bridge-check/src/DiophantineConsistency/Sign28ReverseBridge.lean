import DiophantineConsistency.Sign28ForwardBridge

/-! UNCOMPILED reverse seed-zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed28Sextic.firstResidual p :: SharingSeed28Sextic.remainingResiduals p =
      [SharingSeed28Sextic.firstResidual p,
       Sign28RemainingCuts.newY p,
       Sign28FirstCuts.newE p,
       Sign28RemainingCuts.newkY p,
       Sign28RemainingCuts.newell p,
       Sign28RemainingCuts.newDelta p,
       Sign28FirstCuts.newmainRoot p,
       Sign28FirstCuts.newDc2 p,
       Sign28RemainingCuts.newN1 p,
       Sign28RemainingCuts.newgap p,
       Sign28RemainingCuts.newtau p,
       Sign28RemainingCuts.newN0 p,
       Sign28RemainingCuts.newNt p,
       Sign28RemainingCuts.newcTminusR p,
       Sign28RemainingCuts.newV p,
       Sign28RemainingCuts.newnormalizedS p,
       Sign28RemainingCuts.newV2minusY2 p,
       Sign28FirstCuts.newNa p,
       Sign28FirstCuts.newscaledNs p] := by rfl

theorem backward (p : Fin 4 → ℤ) (beta : V) (v : Fin 32 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed31Sextic.seed p) v) :
    InternalZero (SharingSeed28Sextic.seed p) (Sign28CoordinateRecover.drop v) := by
  have hr := Sign28CoordinateRecover.lift_drop p beta v hp0 hz
  have hz' : InternalZero (SharingSeed31Sextic.seed p) (Sign28FirstCuts.lift beta (Sign28CoordinateRecover.drop v)) := by
    rw [hr]
    exact hz
  have ho := (SharingSign31Squares.seed_zero_iff_residuals p (Sign28FirstCuts.lift beta (Sign28CoordinateRecover.drop v))).mp hz'
  apply (SharingSign28Squares.seed_zero_iff_residuals p (Sign28CoordinateRecover.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.q3_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.Y_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.old_Y_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28FirstCuts.E_eval p beta (Sign28CoordinateRecover.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28FirstCuts.old_E_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.kY_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.old_kY_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.ell_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.old_ell_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.Delta_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.old_Delta_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28FirstCuts.mainRoot_eval p beta (Sign28CoordinateRecover.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28FirstCuts.old_mainRoot_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28FirstCuts.Dc2_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28FirstCuts.old_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.N1_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.old_N1_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.gap_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.old_gap_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.tau_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.old_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.N0_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.old_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.Nt_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.old_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.cTminusR_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.old_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.V_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.old_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.normalizedS_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.old_normalizedS_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28RemainingCuts.V2minusY2_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28RemainingCuts.old_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28FirstCuts.Na_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28FirstCuts.old_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign28FirstCuts.scaledNs_eval p beta (Sign28CoordinateRecover.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign28FirstCuts.old_scaledNs_row p)))))
end DiophantineConsistency.Sign28ZeroBridge
#print axioms DiophantineConsistency.Sign28ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign28ZeroBridge.backward
