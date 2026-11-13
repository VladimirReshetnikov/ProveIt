import DiophantineConsistency.Sign21Transfers00
import DiophantineConsistency.Sign21Transfers01

/-! SOURCE-ONLY forward zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed22Dodecic.firstResidual p :: SharingSeed22Dodecic.remainingResiduals p =
      [Sign21Transfers.oldY p,
       Sign21Transfers.oldE p,
       Sign21Transfers.oldmain_root p,
       Sign21Transfers.oldDc2 p,
       Sign21Transfers.oldtau p,
       Sign21Transfers.oldN0 p,
       Sign21Transfers.oldNt p,
       Sign21Transfers.oldcTminusR p,
       Sign21Transfers.oldV p,
       Sign21Coordinate.oldS p,
       Sign21Transfers.oldV2minusY2 p,
       Sign21Transfers.oldNa p,
       Sign21Transfers.oldscaled_Ns p] := by rfl

theorem forward (p : Fin 4 → ℤ) (v : Fin 22 → V)
    (hz : InternalZero (SharingSeed21Degree14.seed p) v) :
    InternalZero (SharingSeed22Dodecic.seed p) (Sign21Coordinate.lift v) := by
  have hn := (SharingSign21Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign22Squares.seed_zero_iff_residuals p (Sign21Coordinate.lift v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.Y_eval p v)).mpr (by simpa only [Sign21Transfers.new_Y_row] using hn _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.E_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.new_E_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.main_root_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.new_main_root_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.Dc2_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.new_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.tau_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.new_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.N0_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.new_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.Nt_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.new_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.cTminusR_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.new_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.V_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.new_V_row p)))))
  · exact Sign21Coordinate.s_zero p v
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.V2minusY2_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.new_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.Na_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.new_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign21Transfers.scaled_Ns_eval p v)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign21Transfers.new_scaled_Ns_row p)))))
end DiophantineConsistency.Sign21ZeroBridge
#print axioms DiophantineConsistency.Sign21ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign21ZeroBridge.forward
