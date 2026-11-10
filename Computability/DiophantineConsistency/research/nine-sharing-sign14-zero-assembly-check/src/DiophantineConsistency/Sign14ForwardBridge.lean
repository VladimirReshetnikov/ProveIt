import DiophantineConsistency.Sign14Transfer00
import DiophantineConsistency.Sign14Transfer01
import DiophantineConsistency.Sign14Transfer02
import DiophantineConsistency.Sign14Transfer03
import DiophantineConsistency.Sign14Transfer04

/-! SOURCE-ONLY conditional forward zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed15Degree124.firstResidual p :: SharingSeed15Degree124.remainingResiduals p =
      [Sign14Transfers.oldDc2 p,
       Sign14Coordinate.oldD p,
       Sign14Transfers.oldN0 p,
       Sign14Transfers.oldNt p,
       Sign14Transfers.oldNa p,
       Sign14Transfers.oldscaled_Ns p] := by rfl

theorem forward (p : Fin 4 → ℤ) (v : Fin 15 → V) (gap : V)
    (hg : ι gap = (SharingSeed14Degree124.shared36 p).evalRing (fun j => ι (v j)))
    (hz : InternalZero (SharingSeed14Degree124.seed p) v) :
    InternalZero (SharingSeed15Degree124.seed p) (Sign14Coordinate.lift v gap) := by
  have hn := (SharingSign14Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign14Squares.seed_zero_iff_residuals p (Sign14Coordinate.lift v gap)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign14Transfers.Dc2_eval p v gap hg)).mpr (by simpa only [Sign14Transfers.new_Dc2_row] using hn _ List.mem_cons_self)
  · exact Sign14Coordinate.d_zero p v gap hg
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign14Transfers.N0_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign14Transfers.new_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign14Transfers.Nt_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign14Transfers.new_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign14Transfers.Na_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign14Transfers.new_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign14Transfers.scaled_Ns_eval p v gap hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign14Transfers.new_scaled_Ns_row p)))))
end DiophantineConsistency.Sign14ZeroBridge
#print axioms DiophantineConsistency.Sign14ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign14ZeroBridge.forward
