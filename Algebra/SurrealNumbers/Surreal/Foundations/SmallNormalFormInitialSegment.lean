import Surreal.Foundations.SmallNormalFormTruncation

/-!
# Initial segments of small formal normal forms

An initial segment agrees with the larger form at and above every exponent
in its own support. Every proper initial segment is a strict truncation at
the greatest omitted exponent, so its ordinal support length is smaller.
These are statements about the formal carrier and require no evaluation or
arithmetic compatibility with actual surreal numbers.
-/

universe u

namespace Surreal.Foundations.SmallNormalForm

noncomputable section

/-- Agreement through every retained nonzero growth exponent. -/
def IsInitialSegment (F G : SmallNormalForm.{u}) : Prop :=
  ∀ a ∈ support F, ∀ b, a ≤ b → coeff F b = coeff G b

@[refl] theorem IsInitialSegment.refl (F : SmallNormalForm.{u}) : IsInitialSegment F F :=
  fun _ _ _ _ => rfl

theorem IsInitialSegment.coeff_eq {F G : SmallNormalForm.{u}}
    (h : IsInitialSegment F G) {a : SignSequence.{u}} (ha : a ∈ support F) :
    coeff F a = coeff G a := h a ha a le_rfl

theorem IsInitialSegment.support_subset {F G : SmallNormalForm.{u}}
    (h : IsInitialSegment F G) : support F ⊆ support G := by
  intro a ha
  rw [mem_support, ← h.coeff_eq ha]
  exact ha

/-- Initial segments have identical strict earlier parts at retained exponents. -/
theorem IsInitialSegment.trunc_eq {F G : SmallNormalForm.{u}}
    (h : IsInitialSegment F G) {a : SignSequence.{u}} (ha : a ∈ support F) :
    trunc F a = trunc G a := by
  apply ext
  intro b
  by_cases hab : a < b
  · rw [coeff_trunc_of_lt F hab, coeff_trunc_of_lt G hab]
    exact h a ha b hab.le
  · rw [coeff_trunc_of_le F (le_of_not_gt hab), coeff_trunc_of_le G (le_of_not_gt hab)]

@[trans] theorem IsInitialSegment.trans {F G H : SmallNormalForm.{u}}
    (hFG : IsInitialSegment F G) (hGH : IsInitialSegment G H) : IsInitialSegment F H :=
  fun a ha b hab => (hFG a ha b hab).trans (hGH a (hFG.support_subset ha) b hab)

theorem IsInitialSegment.antisymm {F G : SmallNormalForm.{u}}
    (hFG : IsInitialSegment F G) (hGF : IsInitialSegment G F) : F = G := by
  apply ext
  intro a
  by_cases ha : a ∈ support F
  · exact hFG.coeff_eq ha
  · have hga : a ∉ support G := fun h => ha (hGF.support_subset h)
    exact (not_ne_iff.mp ha).trans (not_ne_iff.mp hga).symm

@[simp] theorem zero_isInitialSegment (F : SmallNormalForm.{u}) : IsInitialSegment 0 F := by
  intro a ha
  simp at ha

theorem trunc_isInitialSegment (F : SmallNormalForm.{u}) (a : SignSequence.{u}) :
    IsInitialSegment (trunc F a) F := by
  intro b hb c hbc
  exact coeff_trunc_of_lt F (((mem_support_trunc F a b).mp hb).2.trans_le hbc)

theorem truncIdx_isInitialSegment (F : SmallNormalForm.{u}) (i : Ordinal.{u}) :
    IsInitialSegment (truncIdx F i) F := by
  by_cases hi : i < length F
  · rw [truncIdx_eq_trunc F ⟨i, hi⟩]
    exact trunc_isInitialSegment F _
  · rw [truncIdx_of_length_le F (le_of_not_gt hi)]

/-- A proper initial segment omits a greatest exponent, and retains exactly
the exponents strictly above it. -/
theorem IsInitialSegment.exists_trunc_of_ne {F G : SmallNormalForm.{u}}
    (h : IsInitialSegment F G) (hne : F ≠ G) :
    ∃ a ∈ support G, F = trunc G a := by
  have hex : ∃ a ∈ support G, a ∉ support F := by
    by_contra! hn
    apply hne
    apply ext
    intro a
    by_cases ha : a ∈ support F
    · exact h.coeff_eq ha
    · have hga : a ∉ support G := fun hga => ha (hn a hga)
      exact (not_ne_iff.mp ha).trans (not_ne_iff.mp hga).symm
  have hs : {a : support G | a.val ∉ support F}.Nonempty := by
    obtain ⟨a, ha, haf⟩ := hex
    exact ⟨⟨a, ha⟩, haf⟩
  obtain ⟨a, haf, hmax⟩ :=
    (wellFoundedOn_support G).has_min {a : support G | a.val ∉ support F} hs
  refine ⟨a.val, a.property, ?_⟩
  apply ext
  intro b
  by_cases hab : a.val < b
  · rw [coeff_trunc_of_lt G hab]
    by_cases hb : b ∈ support F
    · exact h.coeff_eq hb
    · have hbg : b ∉ support G := fun hbg => hmax ⟨b, hbg⟩ hb hab
      exact (not_ne_iff.mp hb).trans (not_ne_iff.mp hbg).symm
  · rw [coeff_trunc_of_le G (le_of_not_gt hab)]
    by_contra hb
    have he := h b hb a.val (le_of_not_gt hab)
    exact haf (by rw [mem_support, he]; exact a.property)

theorem isInitialSegment_iff_eq_or_trunc (F G : SmallNormalForm.{u}) :
    IsInitialSegment F G ↔ F = G ∨ ∃ a ∈ support G, F = trunc G a := by
  constructor
  · intro h
    by_cases he : F = G
    · exact Or.inl he
    · exact Or.inr (h.exists_trunc_of_ne he)
  · rintro (rfl | ⟨a, _, rfl⟩)
    · exact IsInitialSegment.refl _
    · exact trunc_isInitialSegment G a

theorem IsInitialSegment.length_le {F G : SmallNormalForm.{u}}
    (h : IsInitialSegment F G) : length F ≤ length G := by
  rcases (isInitialSegment_iff_eq_or_trunc F G).mp h with rfl | ⟨a, ha, rfl⟩
  · exact le_rfl
  · exact (length_trunc_lt G ha).le

theorem IsInitialSegment.length_lt {F G : SmallNormalForm.{u}}
    (h : IsInitialSegment F G) (hne : F ≠ G) : length F < length G := by
  obtain ⟨a, ha, rfl⟩ := h.exists_trunc_of_ne hne
  exact length_trunc_lt G ha

theorem IsInitialSegment.eq_of_length_eq {F G : SmallNormalForm.{u}}
    (h : IsInitialSegment F G) (hlen : length F = length G) : F = G := by
  by_contra hne
  exact (h.length_lt hne).ne hlen

end

end Surreal.Foundations.SmallNormalForm
