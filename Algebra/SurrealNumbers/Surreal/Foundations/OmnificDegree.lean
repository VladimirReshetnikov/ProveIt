import Surreal.Foundations.OmnificIntegers

/-!
# Leading exponents and finite elements of the omnific support ring

The real support and degree prerequisites of `odg:lem:degree` and
`odg:prop:units`. The existing actual leading exponent is identified with
the greatest supported normal-form exponent. Intersecting the finite
valuation ring with the nonnegative-growth-support ring leaves exactly
the ordinary real constants.
-/

universe u
namespace Surreal.Foundations.SignSequence

open SmallNormalForm

noncomputable section

/-- The actual leading exponent is a supported exponent of every nonzero normal form. -/
theorem leadingExponent_mem_normalForm {x : SignSequence.{u}} (hx : x ≠ 0) :
    leadingExponent x ∈ support (normalForm x) := by
  have hF : normalForm x ≠ 0 := by intro h; apply hx; simpa [h] using (cutEvaluation_normalForm x).symm
  have hlen : 0 < length (normalForm x) := bot_lt_iff_ne_bot.mpr ((length_eq_zero _).not.mpr hF)
  have he := (leading_cutEvaluation (normalForm x) hlen).1
  rw [cutEvaluation_normalForm] at he
  rw [he]
  exact exponent_mem_support _ _

/-- Every supported growth exponent is at most the actual leading exponent. -/
theorem normalForm_support_le_leadingExponent (x : SignSequence.{u})
    {a : SignSequence.{u}} (ha : a ∈ support (normalForm x)) : a ≤ leadingExponent x := by
  have hF : normalForm x ≠ 0 := by intro h; simp [h] at ha
  have hlen : 0 < length (normalForm x) := bot_lt_iff_ne_bot.mpr ((length_eq_zero _).not.mpr hF)
  obtain ⟨i, rfl⟩ := exists_exponent_of_mem_support (normalForm x) ha
  have he := (leading_cutEvaluation (normalForm x) hlen).1
  rw [cutEvaluation_normalForm] at he
  rw [he]
  exact (exponent_strictAnti _).antitone (show (⟨0, hlen⟩ : Set.Iio (length (normalForm x))) ≤ i from
    by change (0 : Ordinal.{u}) ≤ i.val; exact bot_le)

/-- No positive growth exponent can occur in a finite surreal. -/
theorem normalForm_coeff_eq_zero_of_finite {x : SignSequence.{u}} (hx : IsFinite x)
    {a : SignSequence.{u}} (ha : 0 < a) : coeff (normalForm x) a = 0 := by
  by_contra hn
  have hx0 : x ≠ 0 := by intro h; simp [h] at hn
  have hb := normalForm_support_le_leadingExponent x hn
  have hv := (isFinite_iff_valuation_nonneg x).mp hx
  rw [valuation_of_ne_zero hx0] at hv
  have hl : leadingExponent x ≤ 0 := by
    have h : (0 : SignSequence.{u}) ≤ -leadingExponent x := WithTop.coe_le_coe.mp hv
    exact neg_nonneg.mp h
  exact (not_lt_of_ge (hb.trans hl)) ha

/-- The real support ring has nonnegative leading growth exponent at every nonzero element. -/
theorem nonnegativeSupport_leadingExponent_nonneg (x : nonnegativeSupportSubring.{u})
    (hx : x.val ≠ 0) : 0 ≤ leadingExponent x.val := by
  by_contra! h
  exact (leadingExponent_mem_normalForm hx)
    ((mem_nonnegativeSupportSubring_iff x.val).mp x.property _ h)

/-- A finite element of the support ring is exactly its ordinary real constant. -/
theorem nonnegativeSupport_eq_realConstant_of_finite (x : nonnegativeSupportSubring.{u})
    (hx : IsFinite x.val) : x = realConstants (constantCoeff x) := by
  apply Subtype.ext
  apply cutEvaluationRingEquiv.symm.injective
  change normalForm x.val = normalForm (ofReal (constantCoeff x))
  rw [normalForm_ofReal]
  apply SmallNormalForm.ext
  intro a
  rw [coeff_single]
  by_cases ha : a = 0
  · subst a
    simp only [ite_true, constantCoeff_eq]
  · rw [if_neg ha]
    rcases lt_or_gt_of_ne ha with h | h
    · exact (mem_nonnegativeSupportSubring_iff x.val).mp x.property a h
    · exact normalForm_coeff_eq_zero_of_finite hx h

/-- Finite elements of the actual nonnegative-support ring are precisely real constants. -/
theorem nonnegativeSupport_isFinite_iff (x : nonnegativeSupportSubring.{u}) :
    IsFinite x.val ↔ ∃ r : ℝ, x = realConstants r := by
  constructor
  · intro hx
    exact ⟨constantCoeff x, nonnegativeSupport_eq_realConstant_of_finite x hx⟩
  · rintro ⟨r, rfl⟩
    exact finite_ofReal r

/-- Nonzero elements of the support ring have valuation at most zero. -/
theorem nonnegativeSupport_valuation_nonpos (x : nonnegativeSupportSubring.{u})
    (hx : x.val ≠ 0) : valuation x.val ≤ 0 := by
  rw [valuation_of_ne_zero hx]
  exact WithTop.coe_le_coe.mpr (neg_nonpos.mpr (nonnegativeSupport_leadingExponent_nonneg x hx))

end
end Surreal.Foundations.SignSequence
