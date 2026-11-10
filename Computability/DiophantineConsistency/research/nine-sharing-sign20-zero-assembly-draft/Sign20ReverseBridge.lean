import DiophantineConsistency.Sign20ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed20Degree20.firstResidual p :: SharingSeed20Degree20.remainingResiduals p =
      [Sign20Transfers.newY p,
       Sign20Transfers.newmain_root p,
       Sign20Transfers.newDc2 p,
       Sign20Transfers.newtau p,
       Sign20Transfers.newN0 p,
       Sign20Transfers.newNt p,
       Sign20Transfers.newcTminusR p,
       Sign20Transfers.newV p,
       Sign20Transfers.newV2minusY2 p,
       Sign20Transfers.newNa p,
       Sign20Transfers.newscaled_Ns p] := by rfl

theorem backward (p : Fin 4 → ℤ) (beta : V) (v : Fin 22 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed21Degree14.seed p) v) :
    InternalZero (SharingSeed20Degree20.seed p) (Sign20Coordinate.drop v) := by
  have hz' : InternalZero (SharingSeed21Degree14.seed p)
      (Sign20Coordinate.lift beta (Sign20Coordinate.drop v)) := by
    rw [Sign20Coordinate.lift_drop p beta v hp0 hz]
    exact hz
  have ho := (SharingSign21Squares.seed_zero_iff_residuals p
    (Sign20Coordinate.lift beta (Sign20Coordinate.drop v))).mp hz'
  apply (SharingSign20Squares.seed_zero_iff_residuals p (Sign20Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.Y_eval p beta (Sign20Coordinate.drop v) hp0)).mp (by simpa only [Sign20Transfers.old_Y_row] using ho _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.main_root_eval p beta (Sign20Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.old_main_root_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.Dc2_eval p beta (Sign20Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.old_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.tau_eval p beta (Sign20Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.old_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.N0_eval p beta (Sign20Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.old_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.Nt_eval p beta (Sign20Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.old_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.cTminusR_eval p beta (Sign20Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.old_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.V_eval p beta (Sign20Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.old_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.V2minusY2_eval p beta (Sign20Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.old_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.Na_eval p beta (Sign20Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.old_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.scaled_Ns_eval p beta (Sign20Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.old_scaled_Ns_row p)))))
end DiophantineConsistency.Sign20ZeroBridge
#print axioms DiophantineConsistency.Sign20ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign20ZeroBridge.backward
