import OAI.Combinatorics.Progressions.Estimates.CommonMarkedMultidegree

namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def realMarkedAffineShift (a : Fin t → ℝ) :
    (ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) →ₗ[ℝ]
      (ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :=
  LinearMap.id + ∑ i, a i •
    ((markedShiftTranslate F v w marked hw hv t (Pi.single i 1)).baseChange ℝ - LinearMap.id)

theorem realMarkedAffineShift_apply (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    realMarkedAffineShift F v w marked hw hv t a p =
      p + ∑ i, a i •
        ((markedShiftTranslate F v w marked hw hv t (Pi.single i 1)).baseChange ℝ p - p) := by
  simp only [realMarkedAffineShift, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply]

theorem realMarkedAffineShift_quotient (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a p) =
      (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ p +
        ⁅realMarkedParameterDirection F v w marked t a,
          (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ p⁆ := by
  let q := (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ
  have hb : ⁅realMarkedParameterDirection F v w marked t a, q p⁆ =
      ∑ i, a i • ⁅realMarkedDirection F v w marked t (Pi.single i 1), q p⁆ := by
    apply (congrArg (fun z : ℝ ⊗[ℚ] MarkedShiftQuotient F v w marked t => ⁅z, q p⁆)
      (realMarkedParameterDirection_apply F v w marked t a)).trans
    apply (sum_lie Finset.univ
      (fun i => a i • realMarkedDirection F v w marked t (Pi.single i 1)) (q p)).trans
    apply Finset.sum_congr rfl
    intro i _
    exact smul_lie (R := ℝ) (a i) (realMarkedDirection F v w marked t (Pi.single i 1)) (q p)
  calc
    q (realMarkedAffineShift F v w marked hw hv t a p) = q p +
        ∑ i, a i • (q ((markedShiftTranslate F v w marked hw hv t (Pi.single i 1)).baseChange ℝ p) - q p) := by
      rw [realMarkedAffineShift_apply F v w marked hw hv t a p]
      simp only [map_add, map_sum, map_smul, map_sub]
    _ = q p + ∑ i, a i • ⁅realMarkedDirection F v w marked t (Pi.single i 1), q p⁆ := by
      apply congrArg (q p + ·)
      apply Finset.sum_congr rfl
      intro i _
      have he := (realMarkedTranslate_quotient F v w marked hw hv t (Pi.single i 1) p).trans
        (realMarkedTranslate_first_order F v w marked hw hv t (Pi.single i 1) (q p))
      rw [he, add_sub_cancel_left]
    _ = _ := congrArg (q p + ·) hb.symm

theorem realMarkedAffineShift_conjugation (hs : 1 ≤ s) (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    conjugationCoord (realMarkedParameterElement F v w marked hw hv t a)
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ p) =
      (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a p) :=
  (realMarkedParameterElement_conjugation F v w marked hw hv t hs a _).trans
    (realMarkedAffineShift_quotient F v w marked hw hv t a p).symm

theorem realMarkedAffineShift_eval (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedShiftEval F v w marked t 0).baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a p) =
      (markedShiftEval F v w marked t 0).baseChange ℝ p +
        ∑ i, a i • ((markedShiftEval F v w marked t (Pi.single i 1)).baseChange ℝ p -
          (markedShiftEval F v w marked t 0).baseChange ℝ p) := by
  rw [realMarkedAffineShift_apply, map_add, map_sum]
  apply congrArg ((markedShiftEval F v w marked t 0).baseChange ℝ p + ·)
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_sub, realMarkedShiftEval_translate, zero_add]

theorem realMarkedAffineShift_eval_affine (a : Fin t → ℝ)
    (p : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t)
    (x : ℝ ⊗[ℚ] L) (y : Fin t → ℝ ⊗[ℚ] L)
    (hp : ∀ b : Fin t → ℚ, (markedShiftEval F v w marked t b).baseChange ℝ p =
      x + ∑ i, (b i : ℝ) • y i) :
    (markedShiftEval F v w marked t 0).baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a p) = x + ∑ i, a i • y i := by
  have h0 : (markedShiftEval F v w marked t 0).baseChange ℝ p = x := by
    simpa only [Pi.zero_apply, Rat.cast_zero, zero_smul, Finset.sum_const_zero, add_zero] using hp 0
  have hi (i : Fin t) : (markedShiftEval F v w marked t (Pi.single i 1)).baseChange ℝ p = x + y i := by
    simpa [Pi.single_apply, apply_ite] using hp (Pi.single i 1)
  rw [realMarkedAffineShift_eval, h0]
  simp only [hi, add_sub_cancel_left]

end Erdos3

end

end OAI
