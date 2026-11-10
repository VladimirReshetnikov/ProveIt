import DiophantineConsistency.Sign18ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign18ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed18Degree94.firstResidual p :: SharingSeed18Degree94.remainingResiduals p =
      [Sign18Transfers.newDc2 p,
       Sign18Transfers.newtau p,
       Sign18Transfers.newN0 p,
       Sign18Transfers.newNt p,
       Sign18Transfers.newcTminusR p,
       Sign18Transfers.newV p,
       Sign18Transfers.newV2minusY2 p,
       Sign18Transfers.newNa p,
       Sign18Transfers.newscaled_Ns p] := by rfl

theorem backward (p : Fin 4 → ℤ) (beta : V) (v : Fin 20 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed19Degree44.seed p) v) :
    InternalZero (SharingSeed18Degree94.seed p) (Sign18Coordinate.drop v) := by
  have hz' : InternalZero (SharingSeed19Degree44.seed p)
      (Sign18Coordinate.lift beta (Sign18Coordinate.drop v)) := by
    rw [Sign18Coordinate.lift_drop p beta v hp0 hz]
    exact hz
  have ho := (SharingSign19Squares.seed_zero_iff_residuals p
    (Sign18Coordinate.lift beta (Sign18Coordinate.drop v))).mp hz'
  apply (SharingSign18Squares.seed_zero_iff_residuals p (Sign18Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.Dc2_eval p beta (Sign18Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.old_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.tau_eval p beta (Sign18Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.old_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.N0_eval p beta (Sign18Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.old_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.Nt_eval p beta (Sign18Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.old_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.cTminusR_eval p beta (Sign18Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.old_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.V_eval p beta (Sign18Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.old_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.V2minusY2_eval p beta (Sign18Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.old_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.Na_eval p beta (Sign18Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.old_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.scaled_Ns_eval p beta (Sign18Coordinate.drop v) hp0)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.old_scaled_Ns_row p)))))
end DiophantineConsistency.Sign18ZeroBridge
#print axioms DiophantineConsistency.Sign18ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign18ZeroBridge.backward
