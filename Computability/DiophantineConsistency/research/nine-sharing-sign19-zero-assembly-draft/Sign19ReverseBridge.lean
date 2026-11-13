import DiophantineConsistency.Sign19ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign19ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed19Degree44.firstResidual p :: SharingSeed19Degree44.remainingResiduals p =
      [Sign19Transfers.newmain_root p,
       Sign19Transfers.newDc2 p,
       Sign19Transfers.newtau p,
       Sign19Transfers.newN0 p,
       Sign19Transfers.newNt p,
       Sign19Transfers.newcTminusR p,
       Sign19Transfers.newV p,
       Sign19Transfers.newV2minusY2 p,
       Sign19Transfers.newNa p,
       Sign19Transfers.newscaled_Ns p] := by rfl

theorem backward (p : Fin 4 → ℤ) (beta : V) (v : Fin 21 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed20Degree20.seed p) v) :
    InternalZero (SharingSeed19Degree44.seed p) (Sign19Coordinate.drop v) := by
  have hz' : InternalZero (SharingSeed20Degree20.seed p)
      (Sign19Coordinate.lift beta (Sign19Coordinate.drop v)) := by
    rw [Sign19Coordinate.lift_drop p beta v hp0 hz]
    exact hz
  have ho := (SharingSign20Squares.seed_zero_iff_residuals p
    (Sign19Coordinate.lift beta (Sign19Coordinate.drop v))).mp hz'
  apply (SharingSign19Squares.seed_zero_iff_residuals p (Sign19Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.main_root_eval p beta (Sign19Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.old_main_root_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.Dc2_eval p beta (Sign19Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.old_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.tau_eval p beta (Sign19Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.old_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.N0_eval p beta (Sign19Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.old_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.Nt_eval p beta (Sign19Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.old_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.cTminusR_eval p beta (Sign19Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.old_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.V_eval p beta (Sign19Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.old_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.V2minusY2_eval p beta (Sign19Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.old_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.Na_eval p beta (Sign19Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.old_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.scaled_Ns_eval p beta (Sign19Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.old_scaled_Ns_row p)))))
end DiophantineConsistency.Sign19ZeroBridge
#print axioms DiophantineConsistency.Sign19ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign19ZeroBridge.backward
