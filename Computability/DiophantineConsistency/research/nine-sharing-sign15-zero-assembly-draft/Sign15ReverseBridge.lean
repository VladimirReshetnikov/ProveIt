import DiophantineConsistency.Sign15ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign15ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed15Degree124.firstResidual p :: SharingSeed15Degree124.remainingResiduals p =
      [Sign15Transfers.newDc2 p,
       Sign15Transfers.newtau p,
       Sign15Transfers.newN0 p,
       Sign15Transfers.newNt p,
       Sign15Transfers.newNa p,
       Sign15Transfers.newscaled_Ns p] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 17 → V)
    (hz : InternalZero (SharingSeed16Degree112.seed p) v) :
    InternalZero (SharingSeed15Degree124.seed p) (Sign15Coordinate.drop v) := by
  have hg : ι (v 16) = (SharingSeed15Degree124.shared31 p).evalRing
      (fun j => ι (Sign15Coordinate.drop v j)) := Sign15Coordinate.old_gap p v hz
  have hz' : InternalZero (SharingSeed16Degree112.seed p)
      (Sign15Coordinate.lift (Sign15Coordinate.drop v) (v 16)) := by
    rw [Sign15Coordinate.lift_drop v]
    exact hz
  have ho := (SharingSign16Squares.seed_zero_iff_residuals p
    (Sign15Coordinate.lift (Sign15Coordinate.drop v) (v 16))).mp hz'
  apply (SharingSign15Squares.seed_zero_iff_residuals p (Sign15Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign15Transfers.Dc2_eval p (Sign15Coordinate.drop v) (v 16) hg)).mp (by simpa only [Sign15Transfers.old_Dc2_row] using ho _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign15Transfers.tau_eval p (Sign15Coordinate.drop v) (v 16) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign15Transfers.old_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign15Transfers.N0_eval p (Sign15Coordinate.drop v) (v 16) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign15Transfers.old_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign15Transfers.Nt_eval p (Sign15Coordinate.drop v) (v 16) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign15Transfers.old_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign15Transfers.Na_eval p (Sign15Coordinate.drop v) (v 16) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign15Transfers.old_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign15Transfers.scaled_Ns_eval p (Sign15Coordinate.drop v) (v 16) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign15Transfers.old_scaled_Ns_row p)))))
end DiophantineConsistency.Sign15ZeroBridge
#print axioms DiophantineConsistency.Sign15ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign15ZeroBridge.backward
