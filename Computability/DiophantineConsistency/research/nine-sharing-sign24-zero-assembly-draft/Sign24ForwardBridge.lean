import DiophantineConsistency.Sign24Transfers00
import DiophantineConsistency.Sign24Transfers01
import DiophantineConsistency.Sign24Transfers02

/-! SOURCE-ONLY forward zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed25Octic.firstResidual p :: SharingSeed25Octic.remainingResiduals p =
      [SharingSeed25Octic.firstResidual p,
       Sign24Transfers.oldY p,
       Sign24Transfers.oldE p,
       Sign24Transfers.oldkY p,
       Sign24Transfers.oldDelta p,
       Sign24Transfers.oldmain_root p,
       Sign24Transfers.oldDc2 p,
       Sign24Transfers.oldtau p,
       Sign24Transfers.oldN0 p,
       Sign24Transfers.oldNt p,
       Sign24Transfers.oldcTminusR p,
       Sign24Transfers.oldV p,
       Sign24Transfers.oldnormalized_S p,
       Sign24Transfers.oldV2minusY2 p,
       Sign24Transfers.oldNa p,
       Sign24Transfers.oldscaled_Ns p] := by rfl

theorem forward (p : Fin 4 → ℤ) (beta : V) (v : Fin 25 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed24Octic.seed p) v) :
    InternalZero (SharingSeed25Octic.seed p) (Sign24Coordinate.lift beta v) := by
  have hn := (SharingSign24Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign25Squares.seed_zero_iff_residuals p (Sign24Coordinate.lift beta v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Sign24Coordinate.q3_zero p beta v hp0
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.Y_eval p beta v hp0)).mpr (by simpa only [Sign24Transfers.new_Y_row] using hn _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.E_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_E_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.kY_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_kY_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.Delta_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_Delta_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.main_root_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_main_root_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.Dc2_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.tau_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.N0_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.Nt_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.cTminusR_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.V_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.normalized_S_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_normalized_S_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.V2minusY2_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.Na_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign24Transfers.scaled_Ns_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign24Transfers.new_scaled_Ns_row p)))))
end DiophantineConsistency.Sign24ZeroBridge
#print axioms DiophantineConsistency.Sign24ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign24ZeroBridge.forward
