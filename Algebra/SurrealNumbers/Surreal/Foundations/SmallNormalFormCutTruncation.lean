import Surreal.Foundations.SmallNormalFormEvaluation

/-!
# Truncation prefixes and residual bounds at every exponent

Every formal truncation evaluates to a sign prefix of the full canonical
candidate. The residual estimate also holds at exponents absent from the
support: either the whole support is earlier, or reverse well-foundedness
selects the greatest omitted exponent and identifies the truncation across
the gap. These proofs do not assume arithmetic preservation of evaluation.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

open SignSequence

noncomputable section

/-- Evaluated earlier terms form a sign prefix of the full candidate. -/
theorem cutEvaluation_trunc_isPrefix (F : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    IsPrefix (cutEvaluation (trunc F a)) (cutEvaluation F) := by
  apply cutEvaluation_isPrefix
  intro b hb
  obtain ⟨hbf, hab⟩ := (mem_support_trunc F a b).mp hb
  rw [trunc_trunc, max_eq_right hab.le, coeff_trunc_of_lt F hab]
  exact cutEvaluation_remainder F b hbf

/-- If every nonzero exponent is earlier than a cutoff, truncation retains the whole form. -/
theorem trunc_eq_self_of_forall_lt (F : SmallNormalForm.{u}) (a : SignSequence.{u})
    (h : ∀ b ∈ support F, a < b) : trunc F a = F := by
  apply ext
  intro b
  by_cases hb : b ∈ support F
  · exact coeff_trunc_of_lt F (h b hb)
  · have hb0 : coeff F b = 0 := not_ne_iff.mp hb
    simp [coeff_trunc, hb0]

/-- Any nonempty support tail below a cutoff has a greatest growth exponent. -/
theorem exists_greatest_support_le (F : SmallNormalForm.{u}) (a : SignSequence.{u})
    (h : ∃ b ∈ support F, b ≤ a) :
    ∃ b ∈ support F, b ≤ a ∧ ∀ c ∈ support F, c ≤ a → c ≤ b := by
  have hn : {b : support F | b.val ≤ a}.Nonempty := by
    obtain ⟨b, hb, hba⟩ := h
    exact ⟨⟨b, hb⟩, hba⟩
  obtain ⟨b, hba, hmax⟩ :=
    (wellFoundedOn_support F).has_min {b : support F | b.val ≤ a} hn
  refine ⟨b.val, b.property, hba, ?_⟩
  intro c hc hca
  exact le_of_not_gt (hmax ⟨c, hc⟩ hca)

/-- With no support between two cutoffs, their strict earlier truncations agree. -/
theorem trunc_eq_trunc_of_support_gap (F : SmallNormalForm.{u}) {a b : SignSequence.{u}}
    (hba : b ≤ a) (hgap : ∀ c ∈ support F, c ≤ a → c ≤ b) :
    trunc F b = trunc F a := by
  apply ext
  intro c
  by_cases hc : c ∈ support F
  · have hiff : b < c ↔ a < c := by
      constructor
      · intro hbc
        exact lt_of_not_ge (fun hca => hbc.not_ge (hgap c hc hca))
      · exact hba.trans_lt
    simp only [coeff_trunc, hiff]
  · have hc0 : coeff F c = 0 := not_ne_iff.mp hc
    simp [coeff_trunc, hc0]

/-- The recursive residual estimate holds at every growth exponent, including
gaps and cutoffs outside the support. -/
theorem cutEvaluation_remainder_all (F : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    (-a : WithTop SignSequence.{u}) < valuation
      (cutEvaluation F - (cutEvaluation (trunc F a) + ofReal (coeff F a) * omegaPower a)) := by
  by_cases ha : a ∈ support F
  · exact cutEvaluation_remainder F a ha
  have ha0 : coeff F a = 0 := not_ne_iff.mp ha
  rw [ha0, map_zero, zero_mul, add_zero]
  by_cases ht : ∃ b ∈ support F, b ≤ a
  · obtain ⟨b, hb, hba, hmax⟩ := exists_greatest_support_le F a ht
    have hlt : b < a := lt_of_le_of_ne hba (by
      intro he
      exact ha (he ▸ hb))
    have htr : trunc F b = trunc F a := trunc_eq_trunc_of_support_gap F hba hmax
    have hscale : (-a : WithTop SignSequence.{u}) < (-b : WithTop SignSequence.{u}) :=
      WithTop.coe_lt_coe.mpr (neg_lt_neg hlt)
    have hr := hscale.trans (cutEvaluation_remainder F b hb)
    have hm : (-a : WithTop SignSequence.{u}) <
        valuation (ofReal (coeff F b) * omegaPower b) := by
      rw [valuation_monomial_of_mem_support F hb]
      exact hscale
    have hv := (lt_min hr hm).trans_le
      (min_valuation_le_add
        (cutEvaluation F - (cutEvaluation (trunc F b) + ofReal (coeff F b) * omegaPower b))
        (ofReal (coeff F b) * omegaPower b))
    have he : cutEvaluation F - cutEvaluation (trunc F a) =
        (cutEvaluation F - (cutEvaluation (trunc F b) + ofReal (coeff F b) * omegaPower b)) +
          ofReal (coeff F b) * omegaPower b := by
      rw [htr]
      abel
    rw [he]
    exact hv
  · have htr : trunc F a = F := trunc_eq_self_of_forall_lt F a (by
      intro b hb
      exact lt_of_not_ge (fun hba => ht ⟨b, hb, hba⟩))
    rw [htr, sub_self, valuation_zero]
    exact WithTop.coe_lt_top (a := (-a : SignSequence.{u}))

end

end Surreal.Foundations.SmallNormalForm
