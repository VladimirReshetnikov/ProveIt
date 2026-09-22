import Surreal.Foundations.SmallNormalForm
import Surreal.Foundations.SignSequenceFiniteLeading

/-!
# Formal truncation and monomial data for small normal forms

These coefficient and support identities supply the formal side of the
future ordinal recursion for normal-form evaluation. The only actual
surreal values used here are individual finite monomial terms.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

noncomputable section

@[simp] theorem coeff_zero (a : SignSequence.{u}) : coeff 0 a = 0 := rfl

@[simp] theorem coeff_add (F G : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    coeff (F + G) a = coeff F a + coeff G a := rfl

@[simp] theorem coeff_sub (F G : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    coeff (F - G) a = coeff F a - coeff G a := rfl

@[simp] theorem support_zero : support (0 : SmallNormalForm.{u}) = ∅ := by
  ext a
  simp

@[simp] theorem support_trunc (F : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    support (trunc F a) = support F ∩ Set.Ioi a := by
  ext b
  simp only [mem_support, coeff_trunc, Set.mem_inter_iff, Set.mem_Ioi]
  by_cases h : a < b <;> simp [h]

theorem mem_support_trunc (F : SmallNormalForm.{u}) (a b : SignSequence.{u}) :
    b ∈ support (trunc F a) ↔ b ∈ support F ∧ a < b := by rw [support_trunc]; rfl

theorem support_trunc_subset (F : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    support (trunc F a) ⊆ support F := by rw [support_trunc]; exact Set.inter_subset_left

theorem coeff_trunc_of_lt (F : SmallNormalForm.{u}) {a b : SignSequence.{u}} (h : a < b) :
    coeff (trunc F a) b = coeff F b := by rw [coeff_trunc, if_pos h]

theorem coeff_trunc_of_le (F : SmallNormalForm.{u}) {a b : SignSequence.{u}} (h : b ≤ a) :
    coeff (trunc F a) b = 0 := by rw [coeff_trunc, if_neg h.not_gt]

theorem coeff_trunc_of_mem (F : SmallNormalForm.{u}) {a b : SignSequence.{u}}
    (hb : b ∈ support (trunc F a)) : coeff (trunc F a) b = coeff F b :=
  coeff_trunc_of_lt F ((support_trunc F a) ▸ hb).2

@[simp] theorem trunc_trunc (F : SmallNormalForm.{u}) (a b : SignSequence.{u}) :
    trunc (trunc F a) b = trunc F (max a b) := by
  apply ext
  intro c
  simp only [coeff_trunc, max_lt_iff]
  by_cases hac : a < c <;> by_cases hbc : b < c <;> simp [hac, hbc]

theorem trunc_eq_zero_of_no_support_gt (F : SmallNormalForm.{u}) (a : SignSequence.{u})
    (h : ∀ b ∈ support F, b ≤ a) : trunc F a = 0 := by
  apply ext
  intro b
  rw [coeff_zero]
  by_cases hb : b ∈ support F
  · exact coeff_trunc_of_le F (h b hb)
  · have hb0 : coeff F b = 0 := not_ne_iff.mp hb
    simp [hb0]

/-- The first growth exponent is the largest support exponent. -/
theorem le_exponent_zero_of_mem_support (F : SmallNormalForm.{u}) (hF : 0 < length F)
    {a : SignSequence.{u}} (ha : a ∈ support F) : a ≤ exponent F ⟨0, hF⟩ := by
  obtain ⟨i, rfl⟩ := exists_exponent_of_mem_support F ha
  apply (exponent_strictAnti F).antitone
  change (0 : Ordinal.{u}) ≤ i.val
  exact zero_le

@[simp] theorem trunc_exponent_zero (F : SmallNormalForm.{u}) (hF : 0 < length F) :
    trunc F (exponent F ⟨0, hF⟩) = 0 :=
  trunc_eq_zero_of_no_support_gt F _ (fun _ ha => le_exponent_zero_of_mem_support F hF ha)

@[simp] theorem truncIdx_zero (F : SmallNormalForm.{u}) : truncIdx F 0 = 0 := by
  apply (length_eq_zero _).mp
  rw [length_truncIdx, min_eq_left zero_le]

/-- A nonzero coefficient at growth exponent `a` has actual valuation `-a`. -/
theorem valuation_monomial_of_mem_support (F : SmallNormalForm.{u}) {a : SignSequence.{u}}
    (ha : a ∈ support F) :
    SignSequence.valuation (SignSequence.ofReal (coeff F a) * SignSequence.omegaPower a) =
      ((-a : SignSequence.{u}) : WithTop SignSequence.{u}) := by
  rw [SignSequence.valuation_mul, SignSequence.valuation_ofReal_of_ne_zero ha,
    SignSequence.valuation_omegaPower, zero_add]

theorem valuation_term (F : SmallNormalForm.{u}) (i : Set.Iio (length F)) :
    SignSequence.valuation (term F i) =
      ((-exponent F i : SignSequence.{u}) : WithTop SignSequence.{u}) := by
  rw [term_of_lt F i.property, ← coeff_exponent]
  exact valuation_monomial_of_mem_support F (exponent_mem_support F i)

/-- Ordinal truncation keeps precisely the earlier support indices. -/
theorem coeff_truncIdx_exponent (F : SmallNormalForm.{u}) (i : Ordinal.{u})
    (j : Set.Iio (length F)) :
    coeff (truncIdx F i) (exponent F j) =
      if (j : Ordinal.{u}) < i then coefficientAt F j else 0 := by
  by_cases hi : i < length F
  · rw [truncIdx_eq_trunc F ⟨i, hi⟩, coeff_trunc, coeff_exponent]
    congr 1
    exact propext (exponent_strictAnti F).lt_iff_gt
  · rw [truncIdx_of_length_le F (le_of_not_gt hi), coeff_exponent,
      if_pos (j.property.trans_le (le_of_not_gt hi))]

theorem mem_support_truncIdx_exponent (F : SmallNormalForm.{u}) (i : Ordinal.{u})
    (j : Set.Iio (length F)) :
    exponent F j ∈ support (truncIdx F i) ↔ (j : Ordinal.{u}) < i := by
  rw [mem_support, coeff_truncIdx_exponent]
  have hc : coefficientAt F j ≠ 0 := (coefficientAt_eq_zero F j).not.mpr (not_le_of_gt j.property)
  by_cases h : (j : Ordinal.{u}) < i <;> simp [h, hc]

theorem support_truncIdx_subset (F : SmallNormalForm.{u}) (i : Ordinal.{u}) :
    support (truncIdx F i) ⊆ support F := by
  by_cases hi : i < length F
  · rw [truncIdx_eq_trunc F ⟨i, hi⟩]
    exact support_trunc_subset F _
  · rw [truncIdx_of_length_le F (le_of_not_gt hi)]

theorem coeff_truncIdx_eq_zero (F : SmallNormalForm.{u}) (i : Ordinal.{u})
    {a : SignSequence.{u}} (ha : coeff F a = 0) : coeff (truncIdx F i) a = 0 := by
  by_contra hn
  exact (support_truncIdx_subset F i hn) ha

/-- Earlier retained coefficients are unchanged by ordinal truncation. -/
theorem coeff_truncIdx_of_mem (F : SmallNormalForm.{u}) (i : Ordinal.{u})
    {a b : SignSequence.{u}} (hab : a ≤ b) (ha : a ∈ support (truncIdx F i)) :
    coeff (truncIdx F i) b = coeff F b :=
  _root_.SurrealHahnSeries.coeff_truncIdx_of_mem
    ((SignSequence.toSurreal_le_iff _ _).mpr hab) ha

theorem trunc_truncIdx_of_mem (F : SmallNormalForm.{u}) (i : Ordinal.{u})
    {a b : SignSequence.{u}} (hab : a ≤ b) (ha : a ∈ support (truncIdx F i)) :
    trunc (truncIdx F i) b = trunc F b :=
  _root_.SurrealHahnSeries.trunc_truncIdx_of_mem
    ((SignSequence.toSurreal_le_iff _ _).mpr hab) ha

/-- A formal single term uses an actual sign-sequence growth exponent. -/
def single (a : SignSequence.{u}) (r : ℝ) : SmallNormalForm.{u} :=
  _root_.SurrealHahnSeries.single (SignSequence.toSurreal a) r

@[simp] theorem coeff_single (a b : SignSequence.{u}) (r : ℝ) :
    coeff (single a r) b = if b = a then r else 0 := by
  simp only [coeff, single, _root_.SurrealHahnSeries.coeff_single, Pi.single_apply,
    SignSequence.toSurreal_inj]

/-- Successor truncation adds precisely the next formal monomial. -/
theorem truncIdx_succ (F : SmallNormalForm.{u}) {i : Ordinal.{u}} (hi : i < length F) :
    truncIdx F (i + 1) = truncIdx F i + single (exponent F ⟨i, hi⟩) (coefficientAt F i) := by
  apply ext
  intro a
  rw [coeff_add, coeff_single]
  by_cases ha : a ∈ support F
  · obtain ⟨j, rfl⟩ := exists_exponent_of_mem_support F ha
    rw [coeff_truncIdx_exponent, coeff_truncIdx_exponent]
    have he : exponent F j = exponent F ⟨i, hi⟩ ↔ (j : Ordinal.{u}) = i := by
      rw [(exponent_strictAnti F).injective.eq_iff, Subtype.mk.injEq]
    simp only [he]
    rcases lt_trichotomy (j : Ordinal.{u}) i with hj | hj | hj
    · have hj' : (j : Ordinal.{u}) < i + 1 := hj.trans (Order.lt_succ i)
      rw [if_pos hj', if_pos hj, if_neg hj.ne, add_zero]
    · simp [hj]
    · have hnot : ¬ (j : Ordinal.{u}) < i + 1 := by
        simpa only [← Order.succ_eq_add_one, Order.lt_succ_iff] using hj.not_ge
      simp [hnot, hj.not_gt, hj.ne']
  · have hz : coeff F a = 0 := not_ne_iff.mp ha
    have hne : a ≠ exponent F ⟨i, hi⟩ := by
      intro h
      exact ha (h ▸ exponent_mem_support F ⟨i, hi⟩)
    rw [coeff_truncIdx_eq_zero F _ hz, coeff_truncIdx_eq_zero F _ hz, if_neg hne, zero_add]

end
end Surreal.Foundations.SmallNormalForm
