import DiophantineConsistency.Sign16ForwardBridge

/-! SOURCE-ONLY reverse zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 Sign16SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem new_rows (p : Fin 4 → ℤ) :
    SharingSeed16Degree112.firstResidual p :: SharingSeed16Degree112.remainingResiduals p =
      [Sign16Transfers.newDc2 p,
       Sign16Transfers.newtau p,
       Sign16Transfers.newN0 p,
       Sign16Transfers.newNt p,
       Sign16Transfers.newcTminusR p,
       Sign16Transfers.newNa p,
       Sign16Transfers.newscaled_Ns p] := by rfl

theorem backward (p : Fin 4 → ℤ) (beta : V) (v : Fin 18 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed17Degree96.seed p) v) :
    InternalZero (SharingSeed16Degree112.seed p) (Sign16Coordinate.drop v) := by
  have hg : ι (v 17) = (ι ((Sign16Coordinate.drop v) 5) + 1) * (ι ((Sign16Coordinate.drop v) 5) + 1) *
      ι ((Sign16Coordinate.drop v) 16) - ι (C beta (Sign16Coordinate.drop v)) := by
    simpa [Sign16Coordinate.drop] using Sign16Coordinate.old_gap p beta v hp0 hz
  have hz' : InternalZero (SharingSeed17Degree96.seed p)
      (Sign16Coordinate.lift (Sign16Coordinate.drop v) (v 17)) := by
    rw [Sign16Coordinate.lift_drop v]
    exact hz
  have ho := (SharingSign17Squares.seed_zero_iff_residuals p
    (Sign16Coordinate.lift (Sign16Coordinate.drop v) (v 17))).mp hz'
  apply (SharingSign16Squares.seed_zero_iff_residuals p (Sign16Coordinate.drop v)).mpr
  intro e he
  rw [new_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign16Transfers.Dc2_eval p beta (Sign16Coordinate.drop v) (v 17) hp0 hg)).mp (by simpa only [Sign16Transfers.old_Dc2_row] using ho _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign16Transfers.tau_eval p beta (Sign16Coordinate.drop v) (v 17) hp0 hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign16Transfers.old_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign16Transfers.N0_eval p beta (Sign16Coordinate.drop v) (v 17) hp0 hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign16Transfers.old_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign16Transfers.Nt_eval p beta (Sign16Coordinate.drop v) (v 17) hp0 hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign16Transfers.old_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign16Transfers.cTminusR_eval p beta (Sign16Coordinate.drop v) (v 17) hp0 hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign16Transfers.old_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign16Transfers.Na_eval p beta (Sign16Coordinate.drop v) (v 17) hp0 hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign16Transfers.old_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign16Transfers.scaled_Ns_eval p beta (Sign16Coordinate.drop v) (v 17) hp0 hg)).mp (ho _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign16Transfers.old_scaled_Ns_row p)))))
end DiophantineConsistency.Sign16ZeroBridge
#print axioms DiophantineConsistency.Sign16ZeroBridge.new_rows
#print axioms DiophantineConsistency.Sign16ZeroBridge.backward
