import DiophantineConsistency.Sign22Transfers00
import DiophantineConsistency.Sign22Transfers01

/-! SOURCE-ONLY forward zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed23Octic.firstResidual p :: SharingSeed23Octic.remainingResiduals p =
      [Sign22Transfers.oldY p,
       Sign22Transfers.oldE p,
       Sign22Coordinate.oldkY p,
       Sign22Transfers.oldmain_root p,
       Sign22Transfers.oldDc2 p,
       Sign22Transfers.oldtau p,
       Sign22Transfers.oldN0 p,
       Sign22Transfers.oldNt p,
       Sign22Transfers.oldcTminusR p,
       Sign22Transfers.oldV p,
       Sign22Transfers.oldnormalized_S p,
       Sign22Transfers.oldV2minusY2 p,
       Sign22Transfers.oldNa p,
       Sign22Transfers.oldscaled_Ns p] := by rfl

theorem forward (p : Fin 4 → ℤ) (v : Fin 23 → V)
    (hz : InternalZero (SharingSeed22Dodecic.seed p) v) :
    InternalZero (SharingSeed23Octic.seed p) (Sign22Coordinate.lift v) := by
  have hn := (SharingSign22Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign23Squares.seed_zero_iff_residuals p (Sign22Coordinate.lift v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.Y_eval p v)).mpr (by simpa only [Sign22Transfers.new_Y_row] using hn _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.E_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.new_E_row p)))))
  · exact Sign22Coordinate.ky_zero p v
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.main_root_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.new_main_root_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.Dc2_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.new_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.tau_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.new_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.N0_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.new_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.Nt_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.new_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.cTminusR_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.new_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.V_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.new_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.normalized_S_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.new_normalized_S_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.V2minusY2_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.new_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.Na_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.new_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign22Transfers.scaled_Ns_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign22Transfers.new_scaled_Ns_row p)))))
end DiophantineConsistency.Sign22ZeroBridge
#print axioms DiophantineConsistency.Sign22ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign22ZeroBridge.forward
