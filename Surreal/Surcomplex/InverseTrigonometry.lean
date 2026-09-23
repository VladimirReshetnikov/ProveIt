import Surreal.Surcomplex.AngleRepresentatives
import Surreal.Surcomplex.Cayley

/-!
# Inverse trigonometry on actual surreal intervals

The existence, uniqueness, order and coordinate clauses of
`trigonometry:thm:inverse` follow from the circle representatives and strict
trigonometric order laws. The domains use actual surreal inequalities;
no finiteness restriction is imposed on the input to inverse tangent.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- Sine is nonnegative precisely on the upper closed semicircle of a full turn. -/
theorem finiteSin_nonneg_iff_of_nonnegativeAngle (θ : SignSequence.FiniteElement.{u})
    (hθ : IsNonnegativeAngle θ) :
    0 ≤ finiteSin θ ↔ θ.val ∈ Set.Icc 0 (SignSequence.ofReal Real.pi) := by
  constructor
  · intro hs
    refine ⟨hθ.1, le_of_not_gt fun h => ?_⟩
    exact (finiteSin_neg_of_mem_Ioo θ ⟨h, hθ.2⟩).not_ge hs
  · rintro ⟨hlo, hhi⟩
    rcases hlo.eq_or_lt with he | he
    · have ht : θ = 0 := ArchimedeanClass.FiniteElement.ext he.symm
      simp [ht]
    rcases hhi.eq_or_lt with he' | he'
    · have ht : θ = SignSequence.finiteOfReal Real.pi :=
        ArchimedeanClass.FiniteElement.ext he'
      simp [ht, Real.sin_pi]
    exact (finiteSin_pos_of_mem_Ioo θ ⟨he, he'⟩).le

/-- Every actual value in `[-1,1]` is attained exactly once by cosine on `[0,pi]`. -/
theorem existsUnique_cos_angle (x : SignSequence.{u}) (hx : x ∈ Set.Icc (-1) 1) :
    ∃! θ : SignSequence.FiniteElement.{u},
      θ.val ∈ Set.Icc 0 (SignSequence.ofReal Real.pi) ∧ finiteCos θ = x := by
  have hs : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  let z : Surcomplex.{u} := ⟨x, SignSequence.sqrt (1 - x ^ 2)⟩
  have hz : modulus z = 1 := by
    apply modulus_eq_of_nonneg_sq (by norm_num)
    change 1 ^ 2 = x ^ 2 + SignSequence.sqrt (1 - x ^ 2) ^ 2
    rw [SignSequence.sqrt_sq hs]
    ring
  obtain ⟨θ, ⟨hθ, he⟩, _⟩ := existsUnique_nonnegative_phase z hz
  have hc : finiteCos θ = x := congrArg QuadraticAlgebra.re he
  have hsin : 0 ≤ finiteSin θ := by
    change 0 ≤ (finitePhase θ).im
    rw [he]
    exact SignSequence.sqrt_nonneg _
  have hi := (finiteSin_nonneg_iff_of_nonnegativeAngle θ hθ).mp hsin
  refine ⟨θ, ⟨hi, hc⟩, ?_⟩
  intro φ hφ
  exact finiteCos_strictAntiOn.injOn hφ.1 hi (hφ.2.trans hc.symm)

/-- Inverse cosine on its full actual domain, with a finite surreal angle as value. -/
def arccos (x : Set.Icc (-1 : SignSequence.{u}) 1) : SignSequence.FiniteElement.{u} :=
  (existsUnique_cos_angle x.val x.property).choose

theorem arccos_mem (x : Set.Icc (-1 : SignSequence.{u}) 1) :
    (arccos x).val ∈ Set.Icc 0 (SignSequence.ofReal Real.pi) :=
  (existsUnique_cos_angle x.val x.property).choose_spec.1.1

@[simp] theorem finiteCos_arccos (x : Set.Icc (-1 : SignSequence.{u}) 1) :
    finiteCos (arccos x) = x.val :=
  (existsUnique_cos_angle x.val x.property).choose_spec.1.2

/-- The unique inverse of cosine reverses the actual surreal order. -/
theorem arccos_strictAnti : StrictAnti (arccos : Set.Icc (-1 : SignSequence.{u}) 1 → _) := by
  intro x y hxy
  by_contra h
  have he := finiteCos_strictAntiOn.antitoneOn (arccos_mem x) (arccos_mem y) (le_of_not_gt h)
  simp only [finiteCos_arccos] at he
  exact (show x.val < y.val from hxy).not_ge he

/-- Inverse sine is the complementary inverse-cosine angle. -/
def arcsin (x : Set.Icc (-1 : SignSequence.{u}) 1) : SignSequence.FiniteElement.{u} :=
  SignSequence.finiteOfReal (Real.pi / 2) - arccos x

theorem arcsin_mem (x : Set.Icc (-1 : SignSequence.{u}) 1) :
    (arcsin x).val ∈ Set.Icc (SignSequence.ofReal (-(Real.pi / 2)))
      (SignSequence.ofReal (Real.pi / 2)) := by
  have h := arccos_mem x
  change SignSequence.ofReal (Real.pi / 2) - (arccos x).val ∈ _
  simp only [Set.mem_Icc, map_neg, map_div₀, map_ofNat] at h ⊢
  constructor <;> linarith [h.1, h.2]

@[simp] theorem finiteSin_arcsin (x : Set.Icc (-1 : SignSequence.{u}) 1) :
    finiteSin (arcsin x) = x.val := by
  simp [arcsin, finiteSin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]

/-- The actual central sine interval maps bijectively onto `[-1,1]`. -/
theorem existsUnique_sin_angle (x : SignSequence.{u}) (hx : x ∈ Set.Icc (-1) 1) :
    ∃! θ : SignSequence.FiniteElement.{u},
      θ.val ∈ Set.Icc (SignSequence.ofReal (-(Real.pi / 2)))
        (SignSequence.ofReal (Real.pi / 2)) ∧ finiteSin θ = x := by
  refine ⟨arcsin ⟨x, hx⟩, ⟨arcsin_mem _, finiteSin_arcsin _⟩, ?_⟩
  intro θ hθ
  exact finiteSin_strictMonoOn.injOn hθ.1 (arcsin_mem _) (hθ.2.trans (finiteSin_arcsin ⟨x, hx⟩).symm)

theorem arcsin_strictMono : StrictMono (arcsin : Set.Icc (-1 : SignSequence.{u}) 1 → _) := by
  intro x y hxy
  change SignSequence.finiteOfReal (Real.pi / 2) - arccos x <
    SignSequence.finiteOfReal (Real.pi / 2) - arccos y
  exact sub_lt_sub_left (arccos_strictAnti hxy) _

/-- The inverse-cosine complement identity holds also at the two endpoints. -/
theorem arccos_eq_pi_div_two_sub_arcsin (x : Set.Icc (-1 : SignSequence.{u}) 1) :
    arccos x = SignSequence.finiteOfReal (Real.pi / 2) - arcsin x := by
  simp [arcsin]

/-- Cosine is nonnegative throughout the closed range of inverse sine. -/
theorem finiteCos_nonneg_of_mem_Icc (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Icc (SignSequence.ofReal (-(Real.pi / 2)))
      (SignSequence.ofReal (Real.pi / 2))) : 0 ≤ finiteCos θ := by
  rcases hθ.1.eq_or_lt with he | he
  · have ht : θ = SignSequence.finiteOfReal (-(Real.pi / 2)) :=
      ArchimedeanClass.FiniteElement.ext he.symm
    simp [ht, Real.cos_pi_div_two]
  rcases hθ.2.eq_or_lt with he' | he'
  · have ht : θ = SignSequence.finiteOfReal (Real.pi / 2) :=
      ArchimedeanClass.FiniteElement.ext he'
    simp [ht, Real.cos_pi_div_two]
  exact (finiteCos_pos_of_mem_Ioo θ ⟨he, he'⟩).le

/-- The other inverse-sine coordinate uses the nonnegative actual square root. -/
theorem finiteCos_arcsin (x : Set.Icc (-1 : SignSequence.{u}) 1) :
    finiteCos (arcsin x) = SignSequence.sqrt (1 - x.val ^ 2) := by
  apply (SignSequence.sqrt_eq_of_nonneg_sq
    (finiteCos_nonneg_of_mem_Icc _ (arcsin_mem x)) _).symm
  have h := finiteCos_sq_add_finiteSin_sq (arcsin x)
  rw [finiteSin_arcsin] at h
  linarith

/-- Interior inputs have interior inverse-sine angles, including infinitesimal endpoint gaps. -/
theorem arcsin_mem_Ioo (x : Set.Icc (-1 : SignSequence.{u}) 1)
    (hx : x.val ∈ Set.Ioo (-1) 1) :
    (arcsin x).val ∈ Set.Ioo (SignSequence.ofReal (-(Real.pi / 2)))
      (SignSequence.ofReal (Real.pi / 2)) := by
  have hi := arcsin_mem x
  have hn : finiteCos (arcsin x) ≠ 0 := by
    rw [finiteCos_arcsin]
    exact (SignSequence.sqrt_pos (by nlinarith [hx.1, hx.2])).ne'
  constructor
  · apply lt_of_le_of_ne hi.1
    intro he
    have ht : arcsin x = SignSequence.finiteOfReal (-(Real.pi / 2)) :=
      ArchimedeanClass.FiniteElement.ext he.symm
    exact hn (by simp [ht, Real.cos_pi_div_two])
  · apply lt_of_le_of_ne hi.2
    intro he
    have ht : arcsin x = SignSequence.finiteOfReal (Real.pi / 2) :=
      ArchimedeanClass.FiniteElement.ext he
    exact hn (by simp [ht, Real.cos_pi_div_two])


/-- The normalized imaginary coordinate of an arbitrary surreal slope is strictly inside `[-1,1]`. -/
theorem normalizedSlope_mem_Ioo (t : SignSequence.{u}) :
    t / SignSequence.sqrt (1 + t ^ 2) ∈ Set.Ioo (-1) 1 := by
  have hp : 0 < 1 + t ^ 2 := by positivity
  have hr := SignSequence.sqrt_pos hp
  have hs := SignSequence.sqrt_sq hp.le
  constructor
  · apply (lt_div_iff₀ hr).mpr
    nlinarith
  · apply (div_lt_iff₀ hr).mpr
    nlinarith

/-- Inverse tangent is defined for all surreal slopes, without a finiteness hypothesis. -/
def arctan (t : SignSequence.{u}) : SignSequence.FiniteElement.{u} :=
  arcsin ⟨t / SignSequence.sqrt (1 + t ^ 2),
    (normalizedSlope_mem_Ioo t).1.le, (normalizedSlope_mem_Ioo t).2.le⟩

theorem arctan_mem (t : SignSequence.{u}) :
    (arctan t).val ∈ Set.Ioo (SignSequence.ofReal (-(Real.pi / 2)))
      (SignSequence.ofReal (Real.pi / 2)) :=
  arcsin_mem_Ioo _ (normalizedSlope_mem_Ioo t)

/-- The sine coordinate of inverse tangent, also for infinite inputs. -/
theorem finiteSin_arctan (t : SignSequence.{u}) :
    finiteSin (arctan t) = t / SignSequence.sqrt (1 + t ^ 2) := finiteSin_arcsin _

/-- The cosine coordinate of inverse tangent is the positive reciprocal radius. -/
theorem finiteCos_arctan (t : SignSequence.{u}) :
    finiteCos (arctan t) = 1 / SignSequence.sqrt (1 + t ^ 2) := by
  rw [arctan, finiteCos_arcsin]
  have hp : 0 < 1 + t ^ 2 := by positivity
  have hr := SignSequence.sqrt_pos hp
  have hs := SignSequence.sqrt_sq hp.le
  apply SignSequence.sqrt_eq_of_nonneg_sq (one_div_nonneg.mpr hr.le)
  change (1 / SignSequence.sqrt (1 + t ^ 2)) ^ 2 =
    1 - (t / SignSequence.sqrt (1 + t ^ 2)) ^ 2
  field_simp
  nlinarith

@[simp] theorem finiteTan_arctan (t : SignSequence.{u}) : finiteTan (arctan t) = t := by
  have hr : SignSequence.sqrt (1 + t ^ 2) ≠ 0 := (SignSequence.sqrt_pos (by positivity)).ne'
  rw [finiteTan, finiteSin_arctan, finiteCos_arctan, div_div_div_cancel_right₀ hr, div_one]

/-- Tangent is strictly increasing on the entire actual central open half-period. -/
theorem finiteTan_strictMonoOn : StrictMonoOn finiteTan
    {θ : SignSequence.FiniteElement.{u} | θ.val ∈ Set.Ioo
      (SignSequence.ofReal (-(Real.pi / 2))) (SignSequence.ofReal (Real.pi / 2))} := by
  intro α hα β hβ hab
  have hcα := finiteCos_pos_of_mem_Ioo α hα
  have hcβ := finiteCos_pos_of_mem_Ioo β hβ
  have hs : 0 < finiteSin (β - α) := by
    apply finiteSin_pos_of_mem_Ioo
    change 0 < β.val - α.val ∧ β.val - α.val < SignSequence.ofReal Real.pi
    have hab' : α.val < β.val := hab
    simp only [Set.mem_Ioo, map_neg, map_div₀, map_ofNat] at hα hβ
    constructor <;> linarith [hα.1, hβ.2]
  rw [finiteSin_sub] at hs
  apply (div_lt_div_iff₀ hcα hcβ).mpr
  nlinarith

/-- Inverse tangent preserves the order at every surreal scale. -/
theorem arctan_strictMono : StrictMono (arctan : SignSequence.{u} → _) := by
  intro x y hxy
  by_contra h
  have he := finiteTan_strictMonoOn.monotoneOn (arctan_mem y) (arctan_mem x) (le_of_not_gt h)
  simp only [finiteTan_arctan] at he
  exact hxy.not_ge he

/-- The second tangent inverse identity has exactly the central open interval as its domain. -/
theorem arctan_finiteTan (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Ioo (SignSequence.ofReal (-(Real.pi / 2)))
      (SignSequence.ofReal (Real.pi / 2))) : arctan (finiteTan θ) = θ :=
  finiteTan_strictMonoOn.injOn (arctan_mem _) hθ (finiteTan_arctan _)

/-- The actual surreal line is order isomorphic to the finite central open angle interval. -/
def arctanOrderIso : SignSequence.{u} ≃o
    {θ : SignSequence.FiniteElement.{u} // θ.val ∈ Set.Ioo
      (SignSequence.ofReal (-(Real.pi / 2))) (SignSequence.ofReal (Real.pi / 2))} where
  toFun t := ⟨arctan t, arctan_mem t⟩
  invFun θ := finiteTan θ.val
  left_inv := finiteTan_arctan
  right_inv θ := Subtype.ext (arctan_finiteTan θ.val θ.property)
  map_rel_iff' := arctan_strictMono.le_iff_le

/-- Every surreal slope has exactly one tangent angle in the actual central open interval. -/
theorem existsUnique_tan_angle (t : SignSequence.{u}) :
    ∃! θ : SignSequence.FiniteElement.{u}, θ.val ∈ Set.Ioo
      (SignSequence.ofReal (-(Real.pi / 2))) (SignSequence.ofReal (Real.pi / 2)) ∧
      finiteTan θ = t := by
  refine ⟨arctan t, ⟨arctan_mem t, finiteTan_arctan t⟩, ?_⟩
  intro θ hθ
  exact finiteTan_strictMonoOn.injOn hθ.1 (arctan_mem t)
    (hθ.2.trans (finiteTan_arctan t).symm)

/-- The half-angle formula for inverse sine is valid even at its two endpoints. -/
theorem arcsin_eq_two_mul_arctan (x : Set.Icc (-1 : SignSequence.{u}) 1) :
    arcsin x = 2 * arctan (x.val / (1 + SignSequence.sqrt (1 - x.val ^ 2))) := by
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono Real.pi_pos
  have hi := arcsin_mem x
  have hh : (finiteHalf (arcsin x)).val ∈ Set.Ioo
      (SignSequence.ofReal (-(Real.pi / 2))) (SignSequence.ofReal (Real.pi / 2)) := by
    rw [val_finiteHalf]
    simp only [Set.mem_Icc, Set.mem_Ioo, map_neg, map_div₀, map_ofNat] at hi ⊢
    constructor <;> linarith [hi.1, hi.2]
  have he := arctan_finiteTan (finiteHalf (arcsin x)) hh
  rw [finiteTan_finiteHalf_eq_finiteSin_div, finiteSin_arcsin, finiteCos_arcsin] at he
  rw [he, two_mul_finiteHalf]


/-- The cosine coordinate of any finite angle lies in the actual closed unit interval. -/
theorem finiteCos_mem_Icc (θ : SignSequence.FiniteElement.{u}) :
    finiteCos θ ∈ Set.Icc (-1) 1 := by
  have h := abs_re_le_modulus (finitePhase θ)
  rw [modulus_finitePhase] at h
  exact abs_le.mp h

/-- The sine coordinate of any finite angle lies in the actual closed unit interval. -/
theorem finiteSin_mem_Icc (θ : SignSequence.FiniteElement.{u}) :
    finiteSin θ ∈ Set.Icc (-1) 1 := by
  have h := abs_im_le_modulus (finitePhase θ)
  rw [modulus_finitePhase] at h
  exact abs_le.mp h

/-- The second cosine inverse identity holds on the prescribed closed angle interval. -/
theorem arccos_finiteCos (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Icc 0 (SignSequence.ofReal Real.pi)) :
    arccos ⟨finiteCos θ, finiteCos_mem_Icc θ⟩ = θ :=
  finiteCos_strictAntiOn.injOn (arccos_mem _) hθ (finiteCos_arccos _)

/-- The second sine inverse identity holds on the prescribed closed angle interval. -/
theorem arcsin_finiteSin (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Icc (SignSequence.ofReal (-(Real.pi / 2)))
      (SignSequence.ofReal (Real.pi / 2))) :
    arcsin ⟨finiteSin θ, finiteSin_mem_Icc θ⟩ = θ :=
  finiteSin_strictMonoOn.injOn (arcsin_mem _) hθ (finiteSin_arcsin _)

/-- Inverse sine is an increasing bijection of the full actual closed intervals. -/
def arcsinOrderIso : Set.Icc (-1 : SignSequence.{u}) 1 ≃o
    {θ : SignSequence.FiniteElement.{u} // θ.val ∈ Set.Icc
      (SignSequence.ofReal (-(Real.pi / 2))) (SignSequence.ofReal (Real.pi / 2))} where
  toFun x := ⟨arcsin x, arcsin_mem x⟩
  invFun θ := ⟨finiteSin θ.val, finiteSin_mem_Icc θ.val⟩
  left_inv x := Subtype.ext (finiteSin_arcsin x)
  right_inv θ := Subtype.ext (arcsin_finiteSin θ.val θ.property)
  map_rel_iff' := arcsin_strictMono.le_iff_le

@[simp] theorem arctan_zero : arctan (0 : SignSequence.{u}) = 0 := by
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal (Real.pi / 2) := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono (half_pos Real.pi_pos)
  simpa only [finiteTan_zero] using arctan_finiteTan (0 : SignSequence.FiniteElement.{u})
    (by
      change SignSequence.ofReal (-(Real.pi / 2)) < (0 : SignSequence.{u}) ∧
        0 < SignSequence.ofReal (Real.pi / 2)
      simpa only [map_neg] using And.intro (neg_neg_of_pos hp) hp)

/-- Inverse tangent is odd, with no restriction on the magnitude of the input. -/
theorem arctan_neg (t : SignSequence.{u}) : arctan (-t) = -arctan t := by
  have hi := arctan_mem t
  have hn : (-arctan t).val ∈ Set.Ioo (SignSequence.ofReal (-(Real.pi / 2)))
      (SignSequence.ofReal (Real.pi / 2)) := by
    change SignSequence.ofReal (-(Real.pi / 2)) < -(arctan t).val ∧
      -(arctan t).val < SignSequence.ofReal (Real.pi / 2)
    simp only [Set.mem_Ioo, map_neg] at hi ⊢
    constructor <;> linarith [hi.1, hi.2]
  simpa only [finiteTan_neg, finiteTan_arctan] using arctan_finiteTan (-arctan t) hn

/-- The exact complementary-angle identity underlying the infinite-slope expansion. -/
theorem arctan_inv_of_pos (t : SignSequence.{u}) (ht : 0 < t) :
    arctan t⁻¹ = SignSequence.finiteOfReal (Real.pi / 2) - arctan t := by
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal (Real.pi / 2) := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono (half_pos Real.pi_pos)
  have hpos : 0 < (arctan t).val := by
    have h := arctan_strictMono ht
    rw [arctan_zero] at h
    exact h
  have hi := arctan_mem t
  have hc : (SignSequence.finiteOfReal (Real.pi / 2) - arctan t).val ∈
      Set.Ioo (SignSequence.ofReal (-(Real.pi / 2))) (SignSequence.ofReal (Real.pi / 2)) := by
    change SignSequence.ofReal (-(Real.pi / 2)) <
        SignSequence.ofReal (Real.pi / 2) - (arctan t).val ∧
      SignSequence.ofReal (Real.pi / 2) - (arctan t).val < SignSequence.ofReal (Real.pi / 2)
    rw [map_neg]
    constructor <;> linarith [hi.2]
  have he := arctan_finiteTan (SignSequence.finiteOfReal (Real.pi / 2) - arctan t) hc
  have htan : finiteTan (SignSequence.finiteOfReal (Real.pi / 2) - arctan t) = t⁻¹ := by
    simp only [finiteTan, finiteSin_sub, finiteCos_sub, finiteSin_constant, finiteCos_constant,
      Real.sin_pi_div_two, Real.cos_pi_div_two, map_one, map_zero, one_mul, zero_mul,
      sub_zero, zero_add, finiteCos_arctan, finiteSin_arctan]
    have hr : SignSequence.sqrt (1 + t ^ 2) ≠ 0 := (SignSequence.sqrt_pos (by positivity)).ne'
    rw [div_div_div_cancel_right₀ hr, one_div]
  rwa [htan] at he

end
end Surreal.Surcomplex
