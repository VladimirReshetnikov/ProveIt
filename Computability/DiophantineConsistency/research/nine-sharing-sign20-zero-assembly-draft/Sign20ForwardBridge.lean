import DiophantineConsistency.Sign20Transfers00
import DiophantineConsistency.Sign20Transfers01

/-! SOURCE-ONLY forward zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed21Degree14.firstResidual p :: SharingSeed21Degree14.remainingResiduals p =
      [Sign20Transfers.oldY p,
       Sign20Coordinate.oldE p,
       Sign20Transfers.oldmain_root p,
       Sign20Transfers.oldDc2 p,
       Sign20Transfers.oldtau p,
       Sign20Transfers.oldN0 p,
       Sign20Transfers.oldNt p,
       Sign20Transfers.oldcTminusR p,
       Sign20Transfers.oldV p,
       Sign20Transfers.oldV2minusY2 p,
       Sign20Transfers.oldNa p,
       Sign20Transfers.oldscaled_Ns p] := by rfl

theorem forward (p : Fin 4 → ℤ) (beta : V) (v : Fin 21 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed20Degree20.seed p) v) :
    InternalZero (SharingSeed21Degree14.seed p) (Sign20Coordinate.lift beta v) := by
  have hn := (SharingSign20Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign21Squares.seed_zero_iff_residuals p (Sign20Coordinate.lift beta v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.Y_eval p beta v hp0)).mpr (by simpa only [Sign20Transfers.new_Y_row] using hn _ List.mem_cons_self)
  · exact Sign20Coordinate.e_zero p beta v hp0
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.main_root_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.new_main_root_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.Dc2_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.new_Dc2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.tau_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.new_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.N0_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.new_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.Nt_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.new_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.cTminusR_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.new_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.V_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.new_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.V2minusY2_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.new_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.Na_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.new_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign20Transfers.scaled_Ns_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign20Transfers.new_scaled_Ns_row p)))))
end DiophantineConsistency.Sign20ZeroBridge
#print axioms DiophantineConsistency.Sign20ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign20ZeroBridge.forward
