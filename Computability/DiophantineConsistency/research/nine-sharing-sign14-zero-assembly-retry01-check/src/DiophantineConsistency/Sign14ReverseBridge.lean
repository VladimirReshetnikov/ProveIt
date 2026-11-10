import DiophantineConsistency.Sign14ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed14Degree124.firstResidual p :: SharingSeed14Degree124.remainingResiduals p =
      [Sign14Transfers.newDc2 p,
       Sign14Transfers.newN0 p,
       Sign14Transfers.newNt p,
       Sign14Transfers.newNa p,
       Sign14Transfers.newscaled_Ns p] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 16 → V)
    (hz : InternalZero (SharingSeed15Degree124.seed p) v) :
    InternalZero (SharingSeed14Degree124.seed p) (Sign14Coordinate.drop v) := by
  have hg : ι (v 15) = (SharingSeed14Degree124.shared36 p).evalRing
      (fun j => ι (Sign14Coordinate.drop v j)) := Sign14Coordinate.old_gap p v hz
  have hz' : InternalZero (SharingSeed15Degree124.seed p)
      (Sign14Coordinate.lift (Sign14Coordinate.drop v) (v 15)) := by
    rw [Sign14Coordinate.lift_drop v]
    exact hz
  have ho := (SharingSign14Squares.seed_zero_iff_residuals p
    (Sign14Coordinate.lift (Sign14Coordinate.drop v) (v 15))).mp hz'
  apply (SharingSign14Squares.seed_zero_iff_residuals p (Sign14Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign14Transfers.Dc2_eval p (Sign14Coordinate.drop v) (v 15) hg)).mp (by simpa only [Sign14Transfers.old_Dc2_row] using ho _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign14Transfers.N0_eval p (Sign14Coordinate.drop v) (v 15) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign14Transfers.old_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign14Transfers.Nt_eval p (Sign14Coordinate.drop v) (v 15) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign14Transfers.old_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign14Transfers.Na_eval p (Sign14Coordinate.drop v) (v 15) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign14Transfers.old_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign14Transfers.scaled_Ns_eval p (Sign14Coordinate.drop v) (v 15) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign14Transfers.old_scaled_Ns_row p)))))
end DiophantineConsistency.Sign14ZeroBridge
#print axioms DiophantineConsistency.Sign14ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign14ZeroBridge.backward
