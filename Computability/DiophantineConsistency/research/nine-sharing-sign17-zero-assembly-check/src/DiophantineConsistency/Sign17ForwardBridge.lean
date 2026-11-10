import DiophantineConsistency.Sign17Transfer00
import DiophantineConsistency.Sign17Transfer01
import DiophantineConsistency.Sign17Transfer02
import DiophantineConsistency.Sign17Transfer03
import DiophantineConsistency.Sign17Transfer04
import DiophantineConsistency.Sign17Transfer05
import DiophantineConsistency.Sign17Transfer06
import DiophantineConsistency.Sign17Transfer07

/-! SOURCE-ONLY conditional forward zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed18Degree94.firstResidual p :: SharingSeed18Degree94.remainingResiduals p =
      [Sign17Transfers.oldDc2 p,
       Sign17Transfers.oldtau p,
       Sign17Transfers.oldN0 p,
       Sign17Transfers.oldNt p,
       Sign17Transfers.oldcTminusR p,
       Sign17Transfers.oldV p,
       Sign17Coordinate.oldD p,
       Sign17Transfers.oldNa p,
       Sign17Transfers.oldscaled_Ns p] := by rfl

theorem forward (p : Fin 4 → ℤ) (v : Fin 18 → V) (gap : V)
    (hg : ι gap = (ι (v 13) + 1) * (ι (v 13) + 1) - ι (v 17) * ι (v 17))
    (hz : InternalZero (SharingSeed17Degree96.seed p) v) :
    InternalZero (SharingSeed18Degree94.seed p) (Sign17Coordinate.lift v gap) := by
  have hn := (SharingSign17Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign18Squares.seed_zero_iff_residuals p (Sign17Coordinate.lift v gap)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.Dc2_eval p v gap hg)).mpr (by simpa only [Sign17Transfers.new_Dc2_row] using hn _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.tau_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.new_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.N0_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.new_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.Nt_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.new_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.cTminusR_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.new_cTminusR_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.V_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.new_V_row p)))))
  · exact Sign17Coordinate.d_zero p v gap hg
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.Na_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.new_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign17Transfers.scaled_Ns_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign17Transfers.new_scaled_Ns_row p)))))
end DiophantineConsistency.Sign17ZeroBridge
#print axioms DiophantineConsistency.Sign17ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign17ZeroBridge.forward
