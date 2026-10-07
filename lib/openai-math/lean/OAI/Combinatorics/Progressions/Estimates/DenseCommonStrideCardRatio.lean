/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.SampledCommonBox

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem IsDenseCommonStrideBox.card_ratio {I : Type*} [Fintype I] [DecidableEq I]
    {N : I → ℕ} {p : ℝ} {A : Finset (I → ℤ)} (h : IsDenseCommonStrideBox N p A) :
    ((integerBox N).card : ℝ) / A.card ≤ Real.exp (p * Fintype.card I) := by
  obtain ⟨c, step, H, hstep, hH, _, hdense, rfl⟩ := h
  rw [commonStrideBox_card c hstep H, card_integerBox, Nat.cast_prod, Nat.cast_prod]
  apply (div_le_iff₀ (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (hH i)))).mpr
  have haxis (i) : (N i : ℝ) ≤ Real.exp p * H i := by
    calc
      _ = Real.exp p * (Real.exp (-p) * (N i : ℝ)) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hdense i) (Real.exp_nonneg _)
  calc
    _ ≤ ∏ i, (Real.exp p * (H i : ℝ)) :=
      Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => haxis i)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      rw [mul_comm (Fintype.card I : ℝ) p]

theorem dense_commonStride_slice_card_ratio {I T : Type*}
    [Fintype I] [DecidableEq I] [Fintype T]
    (e : T → I → ℤ) (he : Function.Injective e) {N : I → ℕ}
    (himage : Finset.univ.image e = integerBox N)
    {p : ℝ} {A : Finset T} (hA : IsDenseCommonStrideBox N p (A.image e)) :
    (Fintype.card T : ℝ) / A.card ≤ Real.exp (p * Fintype.card I) := by
  have hcard : (integerBox N).card = Fintype.card T := by
    rw [← himage, Finset.card_image_of_injective _ he, Finset.card_univ]
  simpa only [hcard, Finset.card_image_of_injective _ he] using hA.card_ratio

end Erdos3

end

end OAI
