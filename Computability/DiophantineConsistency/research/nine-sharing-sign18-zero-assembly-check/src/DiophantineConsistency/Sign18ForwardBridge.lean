import DiophantineConsistency.Sign18Transfer00
import DiophantineConsistency.Sign18Transfer01
import DiophantineConsistency.Sign18Transfer02
import DiophantineConsistency.Sign18Transfer03
import DiophantineConsistency.Sign18Transfer04
import DiophantineConsistency.Sign18Transfer05
import DiophantineConsistency.Sign18Transfer06
import DiophantineConsistency.Sign18Transfer07
import DiophantineConsistency.Sign18Transfer08
/-! SOURCE-ONLY forward zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign18ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed19Degree44.firstResidual p :: SharingSeed19Degree44.remainingResiduals p =
      [SharingSeed19Degree44.firstResidual p,
       Sign18Transfers.oldDc2 p,
       Sign18Transfers.oldtau p,
       Sign18Transfers.oldN0 p,
       Sign18Transfers.oldNt p,
       Sign18Transfers.oldcTminusR p,
       Sign18Transfers.oldV p,
       Sign18Transfers.oldV2minusY2 p,
       Sign18Transfers.oldNa p,
       Sign18Transfers.oldscaled_Ns p] := by rfl

theorem forward (p : Fin 4 → ℤ) (beta : V) (v : Fin 19 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hz : InternalZero (SharingSeed18Degree94.seed p) v) :
    InternalZero (SharingSeed19Degree44.seed p) (Sign18Coordinate.lift beta v) := by
  have hn := (SharingSign18Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign19Squares.seed_zero_iff_residuals p (Sign18Coordinate.lift beta v)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Sign18Coordinate.root_zero p beta v hp0
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.Dc2_eval p beta v hp0)).mpr (by simpa only [Sign18Transfers.new_Dc2_row] using hn _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.tau_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.new_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.N0_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.new_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.Nt_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.new_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.cTminusR_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.new_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.V_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.new_V_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.V2minusY2_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.new_V2minusY2_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.Na_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.new_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign18Transfers.scaled_Ns_eval p beta v hp0)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign18Transfers.new_scaled_Ns_row p)))))
end DiophantineConsistency.Sign18ZeroBridge
#print axioms DiophantineConsistency.Sign18ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign18ZeroBridge.forward
