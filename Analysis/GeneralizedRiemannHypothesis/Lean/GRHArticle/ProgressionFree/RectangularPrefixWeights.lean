import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Transfer of inequalities from rectangular prefixes

On a bounded interval of exponents, a power of a number in `[0,1]` is a
nonnegative combination of prefix indicators. Products of such powers
therefore transfer a weighted inequality from all rectangular prefixes.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- The finite box with inclusive exponent limits. -/
def exponentBox {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ι → ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset fun i ↦ range (L i+1)

/-- Membership in the box means every coordinate is within its limit. -/
theorem mem_exponentBox {ι : Type*} [Fintype ι] [DecidableEq ι] {L a : ι → ℕ} :
    a ∈ exponentBox L ↔ ∀ i, a i ≤ L i := by
  simp only [exponentBox,Fintype.mem_piFinset,mem_range,Nat.lt_succ_iff]

private def prefixPowerCoefficient (t : ℝ) (L j : ℕ) : ℝ :=
  if j = L then t^j else t^j-t^(j+1)

private theorem prefixPowerCoefficient_nonneg {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) (L j : ℕ) :
    0 ≤ prefixPowerCoefficient t L j := by
  unfold prefixPowerCoefficient
  split_ifs
  · exact pow_nonneg h₀ _
  · rw [pow_succ]
    exact sub_nonneg.mpr (mul_le_of_le_one_right (pow_nonneg h₀ _) h₁)

private theorem sum_prefixPowerCoefficient (t : ℝ) {a L : ℕ} (ha : a ≤ L) :
    (∑ j ∈ range (L+1), if a ≤ j then prefixPowerCoefficient t L j else 0) = t^a := by
  rw [← sum_filter]
  have hRange : (range (L+1)).filter (a ≤ ·) = Ico a (L+1) := by
    ext j
    simp only [mem_filter,mem_range,mem_Ico,and_comm]
  rw [hRange,sum_Ico_succ_top ha]
  have hsum (m : ℕ) : (∑ j ∈ range m, (t^j-t^(j+1))) = 1-t^m := by
    induction m with
    | zero => simp
    | succ m hm => rw [sum_range_succ,hm]; ring
  have heq : (∑ j ∈ Ico a L, (t^j-t^(j+1))) = t^a-t^L := by
    rw [sum_Ico_eq_sub _ ha,hsum,hsum]
    ring
  calc
    _ = (∑ j ∈ Ico a L, (t^j-t^(j+1))) + t^L := by
      simp only [prefixPowerCoefficient]
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [if_neg (ne_of_lt (mem_Ico.mp hj).2)]
    _ = _ := by rw [heq]; ring

/-- The sum with geometric weights equals a combination of prefix sums.
A coordinate with ratio one contributes only its full interval. -/
theorem sum_mul_pow_prod_le_zero_of_exponentBox_prefixes {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ι → ℕ) (fixed : Finset ι) (c : (ι → ℕ) → ℝ) (t : ι → ℝ)
    (h₀ : ∀ i, 0 ≤ t i) (h₁ : ∀ i, t i ≤ 1) (hfixed : ∀ i ∈ fixed, t i = 1)
    (hPrefix : ∀ b ∈ exponentBox L, (∀ i ∈ fixed, b i = L i) →
      (∑ a ∈ exponentBox b, c a) ≤ 0) :
    (∑ a ∈ exponentBox L, c a * ∏ i, (t i)^(a i)) ≤ 0 := by
  classical
  let C (b : ι → ℕ) := ∏ i, prefixPowerCoefficient (t i) (L i) (b i)
  have hs (a : ι → ℕ) (ha : a ∈ exponentBox L) :
      (∏ i, (t i)^(a i)) = ∑ b ∈ exponentBox L, if a ∈ exponentBox b then C b else 0 := by
    calc
      _ = ∏ i, ∑ j ∈ range (L i+1), if a i ≤ j then prefixPowerCoefficient (t i) (L i) j else 0 := by
        apply prod_congr rfl
        intro i _
        exact (sum_prefixPowerCoefficient (t i) (mem_exponentBox.mp ha i)).symm
      _ = _ := by
        rw [prod_univ_sum]
        apply sum_congr rfl
        intro b _
        by_cases hb : a ∈ exponentBox b
        · rw [if_pos hb]
          apply prod_congr rfl
          intro i _
          rw [if_pos (mem_exponentBox.mp hb i)]
        · rw [if_neg hb]
          obtain ⟨i,hi⟩ : ∃ i, ¬ a i ≤ b i := by
            by_contra h
            push Not at h
            exact hb (mem_exponentBox.mpr h)
          exact prod_eq_zero (mem_univ i) (if_neg hi)
  have hf (b : ι → ℕ) (hb : b ∈ exponentBox L) :
      ((exponentBox L).filter (· ∈ exponentBox b)) = exponentBox b := by
    ext a
    simp only [mem_filter,and_iff_right_iff_imp]
    intro ha
    exact mem_exponentBox.mpr fun i ↦ (mem_exponentBox.mp ha i).trans (mem_exponentBox.mp hb i)
  have heq :
      (∑ a ∈ exponentBox L, c a * ∏ i, (t i)^(a i)) =
      ∑ b ∈ exponentBox L, (∑ a ∈ exponentBox b, c a) * C b := calc
    _ = ∑ a ∈ exponentBox L, ∑ b ∈ exponentBox L, if a ∈ exponentBox b then c a*C b else 0 := by
      apply sum_congr rfl
      intro a ha
      rw [hs a ha,mul_sum]
      apply sum_congr rfl
      intro b _
      split_ifs <;> simp
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      rw [← sum_filter,hf b hb,sum_mul]
  rw [heq]
  calc
    _ ≤ ∑ b ∈ exponentBox L, (0 : ℝ) := sum_le_sum ?_
    _ = 0 := by simp
  intro b hb
  by_cases he : ∀ i ∈ fixed, b i = L i
  · exact mul_nonpos_of_nonpos_of_nonneg (hPrefix b hb he)
      (prod_nonneg fun i _ ↦ prefixPowerCoefficient_nonneg (h₀ i) (h₁ i) _ _)
  · obtain ⟨i,hi,hn⟩ : ∃ i ∈ fixed, b i ≠ L i := by
      push Not at he
      exact he
    have hC : C b = 0 := prod_eq_zero (mem_univ i) (by simp [prefixPowerCoefficient,hfixed i hi,hn])
    rw [hC,mul_zero]

/-- If rectangular prefix inequalities hold at base denominators, they transfer
to any coordinatewise larger denominators. The coordinates kept equal to the
base need only be tested on their full intervals. -/
theorem sum_mul_reciprocal_pow_prod_le_zero_of_exponentBox_prefixes
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ι → ℕ) (fixed : Finset ι) (c : (ι → ℕ) → ℝ) (b q : ι → ℝ)
    (hb : ∀ i, 0 < b i) (hBQ : ∀ i, b i ≤ q i) (hfixed : ∀ i ∈ fixed, b i = q i)
    (hPrefix : ∀ r ∈ exponentBox L, (∀ i ∈ fixed, r i = L i) →
      (∑ a ∈ exponentBox r, c a * ∏ i, (1/b i)^(a i)) ≤ 0) :
    (∑ a ∈ exponentBox L, c a * ∏ i, (1/q i)^(a i)) ≤ 0 := by
  have hq (i : ι) : 0 < q i := (hb i).trans_le (hBQ i)
  have ht := sum_mul_pow_prod_le_zero_of_exponentBox_prefixes L fixed
    (fun a ↦ c a * ∏ i, (1/b i)^(a i)) (fun i ↦ b i/q i)
    (fun i ↦ div_nonneg (hb i).le (hq i).le)
    (fun i ↦ (div_le_one (hq i)).mpr (hBQ i))
    (fun i hi ↦ (div_eq_one_iff_eq (hq i).ne').mpr (hfixed i hi)) hPrefix
  convert ht using 1
  apply sum_congr rfl
  intro a _
  rw [mul_assoc,← prod_mul_distrib]
  congr 1
  apply prod_congr rfl
  intro i _
  rw [← mul_pow]
  congr 1
  field_simp [(hb i).ne',(hq i).ne']

end GRHArticle.ProgressionFree
