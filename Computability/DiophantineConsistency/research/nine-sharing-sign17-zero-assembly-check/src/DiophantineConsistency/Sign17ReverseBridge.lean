import DiophantineConsistency.Sign17ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed17Degree96.firstResidual p :: SharingSeed17Degree96.remainingResiduals p =
      [Sign17Transfers.newDc2 p,
       Sign17Transfers.newtau p,
       Sign17Transfers.newN0 p,
       Sign17Transfers.newNt p,
       Sign17Transfers.newcTminusR p,
       Sign17Transfers.newV p,
       Sign17Transfers.newNa p,
       Sign17Transfers.newscaled_Ns p] := by rfl

theorem backward (p : Fin 4 → ℤ) (v : Fin 19 → V)
    (hz : InternalZero (SharingSeed18Degree94.seed p) v) :
    InternalZero (SharingSeed17Degree96.seed p) (Sign17Coordinate.drop v) := by
  have hg : ι (v 18) = (ι ((Sign17Coordinate.drop v) 13) + 1) * (ι ((Sign17Coordinate.drop v) 13) + 1) -
      ι ((Sign17Coordinate.drop v) 17) * ι ((Sign17Coordinate.drop v) 17) := by
    simpa [Sign17Coordinate.drop] using Sign17Coordinate.old_gap p v hz
  have hz' : InternalZero (SharingSeed18Degree94.seed p)
      (Sign17Coordinate.lift (Sign17Coordinate.drop v) (v 18)) := by
    rw [Sign17Coordinate.lift_drop v]
    exact hz
  have ho := (SharingSign18Squares.seed_zero_iff_residuals p
    (Sign17Coordinate.lift (Sign17Coordinate.drop v) (v 18))).mp hz'
  apply (SharingSign17Squares.seed_zero_iff_residuals p (Sign17Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.Dc2_eval p (Sign17Coordinate.drop v) (v 18) hg)).mp (by simpa only [Sign17Transfers.old_Dc2_row] using ho _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.tau_eval p (Sign17Coordinate.drop v) (v 18) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.old_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.N0_eval p (Sign17Coordinate.drop v) (v 18) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.old_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.Nt_eval p (Sign17Coordinate.drop v) (v 18) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.old_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.cTminusR_eval p (Sign17Coordinate.drop v) (v 18) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.old_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.V_eval p (Sign17Coordinate.drop v) (v 18) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.old_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.Na_eval p (Sign17Coordinate.drop v) (v 18) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.old_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.scaled_Ns_eval p (Sign17Coordinate.drop v) (v 18) hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.old_scaled_Ns_row p)))))
end DiophantineConsistency.Sign17ZeroBridge
#print axioms DiophantineConsistency.Sign17ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign17ZeroBridge.backward
