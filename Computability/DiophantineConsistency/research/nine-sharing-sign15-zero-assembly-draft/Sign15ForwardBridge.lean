import DiophantineConsistency.Sign15Transfer00
import DiophantineConsistency.Sign15Transfer01
import DiophantineConsistency.Sign15Transfer02
import DiophantineConsistency.Sign15Transfer03
import DiophantineConsistency.Sign15Transfer04
import DiophantineConsistency.Sign15Transfer05

/-! SOURCE-ONLY conditional forward zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign15ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed16Degree112.firstResidual p :: SharingSeed16Degree112.remainingResiduals p =
      [Sign15Transfers.oldDc2 p,
       Sign15Transfers.oldtau p,
       Sign15Transfers.oldN0 p,
       Sign15Transfers.oldNt p,
       Sign15Coordinate.oldD p,
       Sign15Transfers.oldNa p,
       Sign15Transfers.oldscaled_Ns p] := by rfl

theorem forward (p : Fin 4 → ℤ) (v : Fin 16 → V) (gap : V)
    (hg : ι gap = (SharingSeed15Degree124.shared31 p).evalRing (fun j => ι (v j)))
    (hz : InternalZero (SharingSeed15Degree124.seed p) v) :
    InternalZero (SharingSeed16Degree112.seed p) (Sign15Coordinate.lift v gap) := by
  have hn := (SharingSign15Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign16Squares.seed_zero_iff_residuals p (Sign15Coordinate.lift v gap)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign15Transfers.Dc2_eval p v gap hg)).mpr (by simpa only [Sign15Transfers.new_Dc2_row] using hn _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign15Transfers.tau_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign15Transfers.new_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign15Transfers.N0_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign15Transfers.new_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign15Transfers.Nt_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign15Transfers.new_Nt_row p)))))
  · exact Sign15Coordinate.d_zero p v gap hg
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign15Transfers.Na_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign15Transfers.new_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign15Transfers.scaled_Ns_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign15Transfers.new_scaled_Ns_row p)))))
end DiophantineConsistency.Sign15ZeroBridge
#print axioms DiophantineConsistency.Sign15ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign15ZeroBridge.forward
