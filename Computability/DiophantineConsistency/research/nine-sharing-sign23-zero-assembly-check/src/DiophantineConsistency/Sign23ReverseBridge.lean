import DiophantineConsistency.Sign23ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed23Octic.firstResidual p :: SharingSeed23Octic.remainingResiduals p =
      [Sign23Transfers.newY p,
       Sign23Transfers.newE p,
       Sign23Transfers.newkY p,
       Sign23Transfers.newmain_root p,
       Sign23Transfers.newDc2 p,
       Sign23Transfers.newtau p,
       Sign23Transfers.newN0 p,
       Sign23Transfers.newNt p,
       Sign23Transfers.newcTminusR p,
       Sign23Transfers.newV p,
       Sign23Transfers.newnormalized_S p,
       Sign23Transfers.newV2minusY2 p,
       Sign23Transfers.newNa p,
       Sign23Transfers.newscaled_Ns p] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 25 → V)
    (hz : InternalZero (SharingSeed24Octic.seed p) v) :
    InternalZero (SharingSeed23Octic.seed p) (Sign23Coordinate.drop v) := by
  have hz' : InternalZero (SharingSeed24Octic.seed p)
      (Sign23Coordinate.lift (Sign23Coordinate.drop v)) := by
    rw [Sign23Coordinate.lift_drop p v hz]
    exact hz
  have ho := (SharingSign24Squares.seed_zero_iff_residuals p
    (Sign23Coordinate.lift (Sign23Coordinate.drop v))).mp hz'
  apply (SharingSign23Squares.seed_zero_iff_residuals p (Sign23Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.Y_eval p (Sign23Coordinate.drop v))).mp (by simpa only [Sign23Transfers.old_Y_row] using ho _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.E_eval p (Sign23Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.old_E_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.kY_eval p (Sign23Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.old_kY_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.main_root_eval p (Sign23Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.old_main_root_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.Dc2_eval p (Sign23Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.old_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.tau_eval p (Sign23Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.old_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.N0_eval p (Sign23Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.old_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.Nt_eval p (Sign23Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.old_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.cTminusR_eval p (Sign23Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.old_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.V_eval p (Sign23Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.old_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.normalized_S_eval p (Sign23Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.old_normalized_S_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.V2minusY2_eval p (Sign23Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.old_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.Na_eval p (Sign23Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.old_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.scaled_Ns_eval p (Sign23Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.old_scaled_Ns_row p)))))
end DiophantineConsistency.Sign23ZeroBridge
#print axioms DiophantineConsistency.Sign23ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign23ZeroBridge.backward
