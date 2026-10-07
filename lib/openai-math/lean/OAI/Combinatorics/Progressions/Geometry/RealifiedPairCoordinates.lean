/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def realPairEquiv :
    (ℝ ⊗[ℚ] (L × L)) ≃ₗ[ℝ] ((ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) :=
  TensorProduct.prodRight ℚ ℝ ℝ L L

@[simp] theorem realPairEquiv_tmul (r : ℝ) (x : L × L) :
    realPairEquiv (r ⊗ₜ[ℚ] x) = (r ⊗ₜ[ℚ] x.1, r ⊗ₜ[ℚ] x.2) := rfl

theorem realPairEquiv_first (x : ℝ ⊗[ℚ] (L × L)) :
    (realPairEquiv x).1 = (LinearMap.fst ℚ L L).baseChange ℝ x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, Prod.fst_add, hx, hy]

theorem realPairEquiv_second (x : ℝ ⊗[ℚ] (L × L)) :
    (realPairEquiv x).2 = (LinearMap.snd ℚ L L).baseChange ℝ x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, Prod.snd_add, hx, hy]

theorem realPairEquiv_difference (q : ℚ) (x : ℝ ⊗[ℚ] (L × L)) :
    scaledPairDifference q (realPairEquiv x) =
      (scaledPairDifference (L := L) q).baseChange ℝ x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [realPairEquiv_tmul, LinearMap.baseChange_tmul, scaledPairDifference_apply,
      TensorProduct.tmul_sub, TensorProduct.tmul_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI
