import GRHArticle.ProgressionFree.ExponentDigitSliceMass
import GRHArticle.ProgressionFree.RankinHighDigitChargeMap

/-!
# Summing the inequalities on good-high slices

The low-box inequality controls admitted nongreedy vectors whose high
parts are greedy. Fixing such a high part identifies the missing points
with exactly the missing greedy low vectors in that slice.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- The admitted nongreedy vectors with no bad high component. -/
def rankinBadLowVectors {ι : Type*} (k : ι → ℕ) (F : Set (ι → ℕ)) : Set (ι → ℕ) :=
  (F \ rankinExponentVectors ι) \ rankinBadHighVectors k F

private theorem joinExponentDigits_zero {ι : Type*} (k a : ι → ℕ) :
    joinExponentDigits k a 0 = a := by
  funext i
  simp [joinExponentDigits]

private theorem joinExponentDigits_div {ι : Type*} (k a b : ι → ℕ) {i : ι} (ha : a i < 3^(k i)) :
    joinExponentDigits k a b i / 3^(k i) = b i := by
  unfold joinExponentDigits
  rw [Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt ha,zero_add]

/-- A finite low-box inequality, valid for every progression-free slice,
passes to the whole admitted bad-low mass. -/
theorem mul_reciprocalExponentMass_rankinBadLow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (h₁ : ∀ i, u i < 1)
    (k : ι → ℕ) {F : Set (ι → ℕ)} (hF : ThreeAPFree F) (c : ℝ)
    (hBox : ∀ A : Set (ι → ℕ), ThreeAPFree A →
      c * exponentDigitSliceMass u k (A \ rankinExponentVectors ι) 0 ≤
        exponentDigitSliceMass u k (rankinExponentVectors ι \ A) 0) :
    c * reciprocalExponentMass u (rankinBadLowVectors k F) ≤
      reciprocalExponentMass u (rankinExponentVectors ι \ F) := by
  classical
  apply mul_reciprocalExponentMass_le_of_digitSlices u hu h₁ k c
  intro b
  let L := exponentBox (fun i ↦ 3^(k i)-1)
  have h₀ (a : ι → ℕ) (ha : a ∈ L) (i : ι) : a i < 3^(k i) := by
    have h := mem_exponentBox.mp ha i
    have hp : 0 < (3:ℕ)^(k i) := by positivity
    omega
  have hB (a : ι → ℕ) (ha : a ∈ L) (i : ι) :
      joinExponentDigits k a b i/3^(k i) = b i := joinExponentDigits_div k a b (h₀ a ha i)
  by_cases hb : b ∈ rankinExponentVectors ι
  · let A := exponentBoxHighSlice k b F
    have hA : ThreeAPFree A := threeAPFree_exponentBoxHighSlice k b hF
    have he (a : ι → ℕ) (ha : a ∈ L) :
        joinExponentDigits k a b ∈ rankinExponentVectors ι ↔ a ∈ rankinExponentVectors ι := by
      constructor
      · intro h i
        exact ((mem_greedyExponents_add_pow_mul_iff _ _ _ (h₀ a ha i)).mp (h i)).1
      · intro h i
        exact (mem_greedyExponents_add_pow_mul_iff _ _ _ (h₀ a ha i)).mpr ⟨h i,hb i⟩
    have hN (a : ι → ℕ) (ha : a ∈ L) : joinExponentDigits k a b ∉ rankinBadHighVectors k F := by
      rintro ⟨_,i,hi⟩
      rw [hB a ha i] at hi
      exact hi (hb i)
    have hLeft : exponentDigitSliceMass u k (rankinBadLowVectors k F) b =
        exponentDigitSliceMass u k (A \ rankinExponentVectors ι) 0 := by
      unfold exponentDigitSliceMass
      apply sum_congr rfl
      intro a ha
      rw [joinExponentDigits_zero]
      have ha' : a ∈ A ↔ joinExponentDigits k a b ∈ F := ⟨fun hm ↦ hm.2,fun hm ↦ ⟨ha,hm⟩⟩
      have hM : joinExponentDigits k a b ∈ rankinBadLowVectors k F ↔ a ∈ A \ rankinExponentVectors ι := by
        change ((joinExponentDigits k a b ∈ F ∧ joinExponentDigits k a b ∉ rankinExponentVectors ι) ∧
          joinExponentDigits k a b ∉ rankinBadHighVectors k F) ↔ a ∈ A ∧ a ∉ rankinExponentVectors ι
        constructor
        · intro h
          exact ⟨ha'.mpr h.1.1,fun hg ↦ h.1.2 ((he a ha).mpr hg)⟩
        · intro h
          exact ⟨⟨ha'.mp h.1,fun hg ↦ h.2 ((he a ha).mp hg)⟩,hN a ha⟩
      by_cases h : a ∈ A \ rankinExponentVectors ι
      · rw [if_pos ((hM).mpr h),if_pos h]
      · rw [if_neg (fun ha' ↦ h ((hM).mp ha')),if_neg h]
    have hRight : exponentDigitSliceMass u k (rankinExponentVectors ι \ F) b =
        exponentDigitSliceMass u k (rankinExponentVectors ι \ A) 0 := by
      unfold exponentDigitSliceMass
      apply sum_congr rfl
      intro a ha
      rw [joinExponentDigits_zero]
      have ha' : a ∈ A ↔ joinExponentDigits k a b ∈ F := ⟨fun hm ↦ hm.2,fun hm ↦ ⟨ha,hm⟩⟩
      simp only [Set.mem_sdiff,he a ha,ha']
    rw [hLeft,hRight]
    exact hBox A hA
  · have hBad : ∃ i, b i ∉ greedyExponents := by
      by_contra h
      apply hb
      intro i
      by_contra hi
      exact h ⟨i,hi⟩
    obtain ⟨i,hi⟩ := hBad
    have hEmpty : exponentDigitSliceMass u k (rankinBadLowVectors k F) b = 0 := by
      unfold exponentDigitSliceMass
      apply sum_eq_zero
      intro a ha
      apply if_neg
      intro h
      apply h.2
      exact ⟨h.1.1,i,fun hj ↦ hi (hB a ha i ▸ hj)⟩
    rw [hEmpty,mul_zero]
    unfold exponentDigitSliceMass
    exact sum_nonneg (fun a _ ↦ by split_ifs <;> first | exact reciprocalExponentWeight_nonneg hu a | exact le_rfl)

end GRHArticle.ProgressionFree
