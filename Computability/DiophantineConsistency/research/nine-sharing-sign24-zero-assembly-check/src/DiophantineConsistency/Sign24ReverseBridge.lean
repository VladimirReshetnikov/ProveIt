import DiophantineConsistency.Sign24ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed24Octic.firstResidual p :: SharingSeed24Octic.remainingResiduals p =
      [Sign24Transfers.newY p,
       Sign24Transfers.newE p,
       Sign24Transfers.newkY p,
       Sign24Transfers.newDelta p,
       Sign24Transfers.newmain_root p,
       Sign24Transfers.newDc2 p,
       Sign24Transfers.newtau p,
       Sign24Transfers.newN0 p,
       Sign24Transfers.newNt p,
       Sign24Transfers.newcTminusR p,
       Sign24Transfers.newV p,
       Sign24Transfers.newnormalized_S p,
       Sign24Transfers.newV2minusY2 p,
       Sign24Transfers.newNa p,
       Sign24Transfers.newscaled_Ns p] := by rfl

theorem backward (p : Fin 4 → ℤ) (beta : V) (v : Fin 26 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed25Octic.seed p) v) :
    InternalZero (SharingSeed24Octic.seed p) (Sign24Coordinate.drop v) := by
  have hz' : InternalZero (SharingSeed25Octic.seed p)
      (Sign24Coordinate.lift beta (Sign24Coordinate.drop v)) := by
    rw [Sign24Coordinate.lift_drop p beta v hp0 hz]
    exact hz
  have ho := (SharingSign25Squares.seed_zero_iff_residuals p
    (Sign24Coordinate.lift beta (Sign24Coordinate.drop v))).mp hz'
  apply (SharingSign24Squares.seed_zero_iff_residuals p (Sign24Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.Y_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_Y_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.E_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_E_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.kY_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_kY_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.Delta_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_Delta_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.main_root_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_main_root_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.Dc2_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.tau_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.N0_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.Nt_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.cTminusR_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.V_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.normalized_S_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_normalized_S_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.V2minusY2_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.Na_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.scaled_Ns_eval p beta (Sign24Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.old_scaled_Ns_row p)))))
end DiophantineConsistency.Sign24ZeroBridge
#print axioms DiophantineConsistency.Sign24ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign24ZeroBridge.backward
