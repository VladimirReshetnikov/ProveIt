import DiophantineConsistency.Sign21ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed21Degree14.firstResidual p :: SharingSeed21Degree14.remainingResiduals p =
      [Sign21Transfers.newY p,
       Sign21Transfers.newE p,
       Sign21Transfers.newmain_root p,
       Sign21Transfers.newDc2 p,
       Sign21Transfers.newtau p,
       Sign21Transfers.newN0 p,
       Sign21Transfers.newNt p,
       Sign21Transfers.newcTminusR p,
       Sign21Transfers.newV p,
       Sign21Transfers.newV2minusY2 p,
       Sign21Transfers.newNa p,
       Sign21Transfers.newscaled_Ns p] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 23 → V)
    (hz : InternalZero (SharingSeed22Dodecic.seed p) v) :
    InternalZero (SharingSeed21Degree14.seed p) (Sign21Coordinate.drop v) := by
  have hz' : InternalZero (SharingSeed22Dodecic.seed p)
      (Sign21Coordinate.lift (Sign21Coordinate.drop v)) := by
    rw [Sign21Coordinate.lift_drop p v hz]
    exact hz
  have ho := (SharingSign22Squares.seed_zero_iff_residuals p
    (Sign21Coordinate.lift (Sign21Coordinate.drop v))).mp hz'
  apply (SharingSign21Squares.seed_zero_iff_residuals p (Sign21Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.Y_eval p (Sign21Coordinate.drop v))).mp (by simpa only [Sign21Transfers.old_Y_row] using ho _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.E_eval p (Sign21Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.old_E_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.main_root_eval p (Sign21Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.old_main_root_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.Dc2_eval p (Sign21Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.old_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.tau_eval p (Sign21Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.old_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.N0_eval p (Sign21Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.old_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.Nt_eval p (Sign21Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.old_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.cTminusR_eval p (Sign21Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.old_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.V_eval p (Sign21Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.old_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.V2minusY2_eval p (Sign21Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.old_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.Na_eval p (Sign21Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.old_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.scaled_Ns_eval p (Sign21Coordinate.drop v))).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.old_scaled_Ns_row p)))))
end DiophantineConsistency.Sign21ZeroBridge
#print axioms DiophantineConsistency.Sign21ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign21ZeroBridge.backward
