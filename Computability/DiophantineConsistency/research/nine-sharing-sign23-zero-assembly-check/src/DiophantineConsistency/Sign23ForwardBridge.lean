import DiophantineConsistency.Sign23Transfers00
import DiophantineConsistency.Sign23Transfers01

/-! SOURCE-ONLY forward zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed24Octic.firstResidual p :: SharingSeed24Octic.remainingResiduals p =
      [Sign23Transfers.oldY p,
       Sign23Transfers.oldE p,
       Sign23Transfers.oldkY p,
       Sign23Coordinate.oldDelta p,
       Sign23Transfers.oldmain_root p,
       Sign23Transfers.oldDc2 p,
       Sign23Transfers.oldtau p,
       Sign23Transfers.oldN0 p,
       Sign23Transfers.oldNt p,
       Sign23Transfers.oldcTminusR p,
       Sign23Transfers.oldV p,
       Sign23Transfers.oldnormalized_S p,
       Sign23Transfers.oldV2minusY2 p,
       Sign23Transfers.oldNa p,
       Sign23Transfers.oldscaled_Ns p] := by rfl

theorem forward (p : Fin 4 → ℤ) (v : Fin 24 → V)
    (hz : InternalZero (SharingSeed23Octic.seed p) v) :
    InternalZero (SharingSeed24Octic.seed p) (Sign23Coordinate.lift v) := by
  have hn := (SharingSign23Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign24Squares.seed_zero_iff_residuals p (Sign23Coordinate.lift v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.Y_eval p v)).mpr (by simpa only [Sign23Transfers.new_Y_row] using hn _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.E_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.new_E_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.kY_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.new_kY_row p)))))
  · exact Sign23Coordinate.delta_zero p v
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.main_root_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.new_main_root_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.Dc2_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.new_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.tau_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.new_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.N0_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.new_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.Nt_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.new_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.cTminusR_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.new_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.V_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.new_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.normalized_S_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.new_normalized_S_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.V2minusY2_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.new_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.Na_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.new_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign23Transfers.scaled_Ns_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign23Transfers.new_scaled_Ns_row p)))))
end DiophantineConsistency.Sign23ZeroBridge
#print axioms DiophantineConsistency.Sign23ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign23ZeroBridge.forward
