import OAI.Combinatorics.Progressions.Fourier.LocalBohrAlmostPeriodsRelative

namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators Pointwise

variable {N : ℕ}

theorem setAverageTranslate_eq_expect (A : Finset (ZMod N)) (f : ZMod N → ℝ) (x : ZMod N) :
    setAverageTranslate A f x = 𝔼 a ∈ A, f (x - a) := by
  rw [setAverageTranslate, Finset.expect_eq_sum_div_card]

noncomputable def differenceEventProbability
    (A₁ A₂ K : Finset (ZMod N)) (t : ZMod N) : ℝ :=
  𝔼 a ∈ A₁, 𝔼 b ∈ A₂, realSetIndicator K (a - b + t)

theorem differenceEventProbability_eq_triple
    (A₁ A₂ K : Finset (ZMod N)) (t : ZMod N) :
    differenceEventProbability A₁ A₂ K t =
      setAverageTranslate (-A₁) (setAverageTranslate A₂ (realSetIndicator K)) t := by
  rw [differenceEventProbability, setAverageTranslate_eq_expect, Finset.expect_neg_index]
  apply Finset.expect_congr rfl
  intro a _
  rw [setAverageTranslate_eq_expect]
  apply Finset.expect_congr rfl
  intro b _
  congr 1
  abel

noncomputable def smoothedDifferenceEventProbability
    (A₁ A₂ K R : Finset (ZMod N)) : ℝ :=
  𝔼 t ∈ R, differenceEventProbability A₁ A₂ K t

theorem smoothedDifferenceEventProbability_eq_average
    (A₁ A₂ K R : Finset (ZMod N)) :
    smoothedDifferenceEventProbability A₁ A₂ K R =
      𝔼 a ∈ A₁, 𝔼 b ∈ A₂, 𝔼 t ∈ R, realSetIndicator K (a - b + t) := by
  unfold smoothedDifferenceEventProbability differenceEventProbability
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro a _
  rw [Finset.expect_comm]

theorem smoothedDifferenceEventProbability_sub_le
    (A₁ A₂ K : Finset (ZMod N)) {R : Finset (ZMod N)} (hR : R.Nonempty) {epsilon : ℝ}
    (hshift : ∀ t ∈ R,
      |differenceEventProbability A₁ A₂ K t - differenceEventProbability A₁ A₂ K 0| ≤ epsilon) :
    |smoothedDifferenceEventProbability A₁ A₂ K R - differenceEventProbability A₁ A₂ K 0| ≤
      epsilon := by
  have heq : smoothedDifferenceEventProbability A₁ A₂ K R - differenceEventProbability A₁ A₂ K 0 =
      𝔼 t ∈ R, (differenceEventProbability A₁ A₂ K t - differenceEventProbability A₁ A₂ K 0) := by
    rw [Finset.expect_sub_distrib, Finset.expect_const hR]
    rfl
  rw [heq]
  have hnorm := RCLike.norm_expect_le (K := ℝ)
    (f := fun t => differenceEventProbability A₁ A₂ K t - differenceEventProbability A₁ A₂ K 0)
    (s := R)
  calc
    _ ≤ 𝔼 t ∈ R, |differenceEventProbability A₁ A₂ K t - differenceEventProbability A₁ A₂ K 0| := by
      simpa only [Real.norm_eq_abs] using hnorm
    _ ≤ 𝔼 _t ∈ R, epsilon := Finset.expect_le_expect hshift
    _ = epsilon := Finset.expect_const hR epsilon

theorem differenceEventProbability_smoothing_of_triple_shifts
    (A₁ A₂ K : Finset (ZMod N)) {R : Finset (ZMod N)} (hR : R.Nonempty) {epsilon : ℝ}
    (hshift : ∀ t ∈ R, ∀ x,
      |setAverageTranslate (-A₁) (setAverageTranslate A₂ (realSetIndicator K)) (x + t) -
        setAverageTranslate (-A₁) (setAverageTranslate A₂ (realSetIndicator K)) x| ≤ epsilon) :
    |smoothedDifferenceEventProbability A₁ A₂ K R - differenceEventProbability A₁ A₂ K 0| ≤
      epsilon := by
  apply smoothedDifferenceEventProbability_sub_le A₁ A₂ K hR
  intro t ht
  simpa only [differenceEventProbability_eq_triple, zero_add] using hshift t ht 0

end Erdos3.CyclicCrootSisask

end

end OAI
