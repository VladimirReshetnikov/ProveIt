import DiophantineConsistency.Sign22ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed22Dodecic.firstResidual p :: SharingSeed22Dodecic.remainingResiduals p =
      [Sign22Transfers.newY p,
       Sign22Transfers.newE p,
       Sign22Transfers.newmain_root p,
       Sign22Transfers.newDc2 p,
       Sign22Transfers.newtau p,
       Sign22Transfers.newN0 p,
       Sign22Transfers.newNt p,
       Sign22Transfers.newcTminusR p,
       Sign22Transfers.newV p,
       Sign22Transfers.newnormalized_S p,
       Sign22Transfers.newV2minusY2 p,
       Sign22Transfers.newNa p,
       Sign22Transfers.newscaled_Ns p] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 24 → V)
    (hz : InternalZero (SharingSeed23Octic.seed p) v) :
    InternalZero (SharingSeed22Dodecic.seed p) (Sign22Coordinate.drop v) := by
  have hz' : InternalZero (SharingSeed23Octic.seed p)
      (Sign22Coordinate.lift (Sign22Coordinate.drop v)) := by
    rw [Sign22Coordinate.lift_drop p v hz]
    exact hz
  have ho := (SharingSign23Squares.seed_zero_iff_residuals p
    (Sign22Coordinate.lift (Sign22Coordinate.drop v))).mp hz'
  apply (SharingSign22Squares.seed_zero_iff_residuals p (Sign22Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.Y_eval p (Sign22Coordinate.drop v))).mp (by simpa only [Sign22Transfers.old_Y_row] using ho _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.E_eval p (Sign22Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.old_E_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.main_root_eval p (Sign22Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.old_main_root_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.Dc2_eval p (Sign22Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.old_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.tau_eval p (Sign22Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.old_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.N0_eval p (Sign22Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.old_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.Nt_eval p (Sign22Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.old_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.cTminusR_eval p (Sign22Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.old_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.V_eval p (Sign22Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.old_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.normalized_S_eval p (Sign22Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.old_normalized_S_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.V2minusY2_eval p (Sign22Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.old_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.Na_eval p (Sign22Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.old_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.scaled_Ns_eval p (Sign22Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.old_scaled_Ns_row p)))))
end DiophantineConsistency.Sign22ZeroBridge
#print axioms DiophantineConsistency.Sign22ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign22ZeroBridge.backward
