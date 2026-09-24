import Surreal.Surcomplex.InverseTrigonometry

/-!
# Interior angles at arbitrary surreal scales

The normalized dot product and absolute determinant of two noncollinear
actual surcomplex vectors determine a unique angle in `(0, pi)`. This is
the construction in `trigonometry:eq:interiorangle`; the cosine and area
identities also supply prerequisites for `trigonometry:thm:trianglelaws`.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- A nonzero determinant forces the first vector to be nonzero. -/
theorem left_ne_zero_of_cross_ne_zero {z w : Surcomplex.{u}}
    (h : Complexify.cross z w ≠ 0) : z ≠ 0 := by
  intro hz
  simp [Complexify.cross_def, hz] at h

/-- A nonzero determinant forces the second vector to be nonzero. -/
theorem right_ne_zero_of_cross_ne_zero {z w : Surcomplex.{u}}
    (h : Complexify.cross z w ≠ 0) : w ≠ 0 := by
  intro hw
  simp [Complexify.cross_def, hw] at h

/-- A noncollinear triangle has strictly positive actual surreal area. -/
theorem triangleArea_pos_of_cross_ne_zero {z w : Surcomplex.{u}}
    (h : Complexify.cross z w ≠ 0) : 0 < triangleArea z w :=
  div_pos (abs_pos.mpr h) (by norm_num)

/-- The upper-semicircle direction specified by the dot product and absolute determinant. -/
def interiorDirection (z w : Surcomplex.{u}) : Surcomplex.{u} :=
  ⟨Complexify.dot z w / (modulus z * modulus w),
    |Complexify.cross z w| / (modulus z * modulus w)⟩

/-- Gram's identity puts the normalized interior direction on the actual unit circle. -/
theorem modulus_interiorDirection (z w : Surcomplex.{u}) (hz : z ≠ 0) (hw : w ≠ 0) :
    modulus (interiorDirection z w) = 1 := by
  apply modulus_eq_of_nonneg_sq (by norm_num)
  change 1 ^ 2 = (Complexify.dot z w / (modulus z * modulus w)) ^ 2 +
    (|Complexify.cross z w| / (modulus z * modulus w)) ^ 2
  rw [div_pow, div_pow, sq_abs, ← add_div, Complexify.dot_sq_add_cross_sq,
    mul_pow, modulus_sq, modulus_sq]
  change 1 ^ 2 = (normSq z * normSq w) / (normSq z * normSq w)
  rw [div_self (mul_ne_zero (normSq_pos hz).ne' (normSq_pos hw).ne'), one_pow]

/-- Noncollinearity places the normalized direction strictly above the real axis. -/
theorem interiorDirection_im_pos (z w : Surcomplex.{u}) (h : Complexify.cross z w ≠ 0) :
    0 < (interiorDirection z w).im :=
  div_pos (abs_pos.mpr h) (mul_pos (modulus_pos (left_ne_zero_of_cross_ne_zero h))
    (modulus_pos (right_ne_zero_of_cross_ne_zero h)))

/-- The prescribed cosine and positive sine have exactly one angle in the actual interval `(0,pi)`. -/
theorem existsUnique_interiorAngle (z w : Surcomplex.{u}) (h : Complexify.cross z w ≠ 0) :
    ∃! θ : SignSequence.FiniteElement.{u},
      θ.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) ∧
        finitePhase θ = interiorDirection z w := by
  obtain ⟨θ, ⟨hθ, he⟩, _⟩ := existsUnique_nonnegative_phase (interiorDirection z w)
    (modulus_interiorDirection z w (left_ne_zero_of_cross_ne_zero h)
      (right_ne_zero_of_cross_ne_zero h))
  have hs : 0 < finiteSin θ := by
    change 0 < (finitePhase θ).im
    rw [he]
    exact interiorDirection_im_pos z w h
  have hi := (finiteSin_pos_iff_of_nonnegativeAngle θ hθ).mp hs
  refine ⟨θ, ⟨hi, he⟩, ?_⟩
  intro φ hφ
  apply finiteCos_strictAntiOn.injOn ⟨hφ.1.1.le, hφ.1.2.le⟩ ⟨hi.1.le, hi.2.le⟩
  exact congrArg (fun x : Surcomplex.{u} => x.re) (hφ.2.trans he.symm)

/-- The interior angle between two noncollinear vectors, with no restriction on their scales. -/
def interiorAngle (z w : Surcomplex.{u}) (h : Complexify.cross z w ≠ 0) :
    SignSequence.FiniteElement.{u} := (existsUnique_interiorAngle z w h).choose

theorem interiorAngle_mem (z w : Surcomplex.{u}) (h : Complexify.cross z w ≠ 0) :
    (interiorAngle z w h).val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) :=
  (existsUnique_interiorAngle z w h).choose_spec.1.1

theorem finitePhase_interiorAngle (z w : Surcomplex.{u}) (h : Complexify.cross z w ≠ 0) :
    finitePhase (interiorAngle z w h) = interiorDirection z w :=
  (existsUnique_interiorAngle z w h).choose_spec.1.2

/-- The cosine coordinate of the actual interior angle. -/
theorem finiteCos_interiorAngle (z w : Surcomplex.{u}) (h : Complexify.cross z w ≠ 0) :
    finiteCos (interiorAngle z w h) = Complexify.dot z w / (modulus z * modulus w) :=
  congrArg (fun x : Surcomplex.{u} => x.re) (finitePhase_interiorAngle z w h)

/-- The sine coordinate of the actual interior angle. -/
theorem finiteSin_interiorAngle (z w : Surcomplex.{u}) (h : Complexify.cross z w ≠ 0) :
    finiteSin (interiorAngle z w h) = |Complexify.cross z w| / (modulus z * modulus w) :=
  congrArg (fun x : Surcomplex.{u} => x.im) (finitePhase_interiorAngle z w h)

/-- The area form of the sine coordinate in the manuscript's interior-angle definition. -/
theorem finiteSin_interiorAngle_area (z w : Surcomplex.{u}) (h : Complexify.cross z w ≠ 0) :
    finiteSin (interiorAngle z w h) = 2 * triangleArea z w / (modulus z * modulus w) := by
  rw [finiteSin_interiorAngle]
  change |Complexify.cross z w| / _ = 2 * (|Complexify.cross z w| / 2) / _
  ring

/-- The upper-semicircle direction is independent of the ordering of its two vectors. -/
theorem interiorDirection_comm (z w : Surcomplex.{u}) :
    interiorDirection z w = interiorDirection w z := by
  ext
  · simp only [interiorDirection, Complexify.dot_comm z w, mul_comm]
  · simp only [interiorDirection, Complexify.cross_swap z w, abs_neg, mul_comm]

/-- The actual interior angle is independent of the ordering of its two vectors. -/
theorem interiorAngle_comm (z w : Surcomplex.{u}) (h : Complexify.cross z w ≠ 0)
    (h' : Complexify.cross w z ≠ 0) : interiorAngle z w h = interiorAngle w z h' := by
  apply (existsUnique_interiorAngle w z h').choose_spec.2
  exact ⟨interiorAngle_mem z w h,
    (finitePhase_interiorAngle z w h).trans (interiorDirection_comm z w)⟩

/-- The cosine law for the side opposite an actual interior angle. -/
theorem interiorAngle_cosine_law (z w : Surcomplex.{u}) (h : Complexify.cross z w ≠ 0) :
    modulus (z - w) ^ 2 = modulus z ^ 2 + modulus w ^ 2 -
      2 * modulus z * modulus w * finiteCos (interiorAngle z w h) := by
  rw [finiteCos_interiorAngle]
  have hm : modulus z * modulus w ≠ 0 :=
    mul_ne_zero (modulus_pos (left_ne_zero_of_cross_ne_zero h)).ne'
      (modulus_pos (right_ne_zero_of_cross_ne_zero h)).ne'
  have he : 2 * modulus z * modulus w *
      (Complexify.dot z w / (modulus z * modulus w)) = 2 * Complexify.dot z w := by
    calc
      _ = 2 * ((modulus z * modulus w) *
        (Complexify.dot z w / (modulus z * modulus w))) := by ring
      _ = _ := by rw [mul_div_cancel₀ _ hm]
  rw [he, modulus_sq, modulus_sq, modulus_sq]
  exact Complexify.normSq_sub z w

/-- Area equals half the product of adjacent lengths and the sine of their included angle. -/
theorem interiorAngle_area (z w : Surcomplex.{u}) (h : Complexify.cross z w ≠ 0) :
    triangleArea z w = modulus z * modulus w * finiteSin (interiorAngle z w h) / 2 := by
  rw [finiteSin_interiorAngle, mul_div_cancel₀ _
    (mul_ne_zero (modulus_pos (left_ne_zero_of_cross_ne_zero h)).ne'
      (modulus_pos (right_ne_zero_of_cross_ne_zero h)).ne')]
  rfl

end
end Surreal.Surcomplex
