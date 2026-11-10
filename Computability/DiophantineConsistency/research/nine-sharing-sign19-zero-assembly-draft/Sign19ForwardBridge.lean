import DiophantineConsistency.Sign19Transfers00
import DiophantineConsistency.Sign19Transfers01
/-! SOURCE-ONLY forward zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign19ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed20Degree20.firstResidual p :: SharingSeed20Degree20.remainingResiduals p =
      [SharingSeed20Degree20.firstResidual p,
       Sign19Transfers.oldmain_root p,
       Sign19Transfers.oldDc2 p,
       Sign19Transfers.oldtau p,
       Sign19Transfers.oldN0 p,
       Sign19Transfers.oldNt p,
       Sign19Transfers.oldcTminusR p,
       Sign19Transfers.oldV p,
       Sign19Transfers.oldV2minusY2 p,
       Sign19Transfers.oldNa p,
       Sign19Transfers.oldscaled_Ns p] := by rfl

theorem forward (p : Fin 4 → ℤ) (beta : V) (v : Fin 20 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed19Degree44.seed p) v) :
    InternalZero (SharingSeed20Degree20.seed p) (Sign19Coordinate.lift beta v) := by
  have hn := (SharingSign19Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign20Squares.seed_zero_iff_residuals p (Sign19Coordinate.lift beta v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Sign19Coordinate.y_zero p beta v hp0
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.main_root_eval p beta v hp0)).mpr (by simpa only [Sign19Transfers.new_main_root_row] using hn _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.Dc2_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.new_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.tau_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.new_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.N0_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.new_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.Nt_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.new_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.cTminusR_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.new_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.V_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.new_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.V2minusY2_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.new_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.Na_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.new_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign19Transfers.scaled_Ns_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign19Transfers.new_scaled_Ns_row p)))))
end DiophantineConsistency.Sign19ZeroBridge
#print axioms DiophantineConsistency.Sign19ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign19ZeroBridge.forward
