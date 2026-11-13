import DiophantineConsistency.Sign16Transfer00
import DiophantineConsistency.Sign16Transfer01
import DiophantineConsistency.Sign16Transfer02
import DiophantineConsistency.Sign16Transfer03
import DiophantineConsistency.Sign16Transfer04
import DiophantineConsistency.Sign16Transfer05
import DiophantineConsistency.Sign16Transfer06

/-! SOURCE-ONLY conditional forward zero assembly. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 Sign16SharedValues
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zero_iff_of_eval_eq {σ τ : Type*} (a : Expr σ) (b : Expr τ) (v : σ → V) (w : τ → V)
    (he : a.evalRing (fun i => ι (v i)) = b.evalRing (fun i => ι (w i))) :
    InternalZero a v ↔ InternalZero b w := by
  rw [internalZero_iff, internalZero_iff, he]

theorem old_rows (p : Fin 4 → ℤ) :
    SharingSeed17Degree96.firstResidual p :: SharingSeed17Degree96.remainingResiduals p =
      [Sign16Transfers.oldDc2 p,
       Sign16Transfers.oldtau p,
       Sign16Transfers.oldN0 p,
       Sign16Transfers.oldNt p,
       Sign16Transfers.oldcTminusR p,
       Sign16Coordinate.oldD p,
       Sign16Transfers.oldNa p,
       Sign16Transfers.oldscaled_Ns p] := by rfl

theorem forward (p : Fin 4 → ℤ) (beta : V) (v : Fin 17 → V) (gap : V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)
    (hg : ι gap = (ι (v 5) + 1) * (ι (v 5) + 1) * ι (v 16) - ι (C beta v))
    (hz : InternalZero (SharingSeed16Degree112.seed p) v) :
    InternalZero (SharingSeed17Degree96.seed p) (Sign16Coordinate.lift v gap) := by
  have hn := (SharingSign16Squares.seed_zero_iff_residuals p v).mp hz
  apply (SharingSign17Squares.seed_zero_iff_residuals p (Sign16Coordinate.lift v gap)).mpr
  intro e he
  rw [old_rows p] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign16Transfers.Dc2_eval p beta v gap hp0 hg)).mpr (by simpa only [Sign16Transfers.new_Dc2_row] using hn _ List.mem_cons_self)
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign16Transfers.tau_eval p beta v gap hp0 hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign16Transfers.new_tau_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign16Transfers.N0_eval p beta v gap hp0 hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign16Transfers.new_N0_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign16Transfers.Nt_eval p beta v gap hp0 hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign16Transfers.new_Nt_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign16Transfers.cTminusR_eval p beta v gap hp0 hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign16Transfers.new_cTminusR_row p)))))
  · exact Sign16Coordinate.d_zero p beta v gap hp0 hg
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign16Transfers.Na_eval p beta v gap hp0 hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign16Transfers.new_Na_row p)))))
  · exact (zero_iff_of_eval_eq _ _ _ _ (Sign16Transfers.scaled_Ns_eval p beta v gap hp0 hg)).mpr (hn _ (List.mem_cons_of_mem _ (List.mem_of_mem_drop (List.mem_of_head? (Sign16Transfers.new_scaled_Ns_row p)))))
end DiophantineConsistency.Sign16ZeroBridge
#print axioms DiophantineConsistency.Sign16ZeroBridge.old_rows
#print axioms DiophantineConsistency.Sign16ZeroBridge.forward
