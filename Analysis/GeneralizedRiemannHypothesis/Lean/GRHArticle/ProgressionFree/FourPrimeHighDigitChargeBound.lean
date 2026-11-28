import GRHArticle.ProgressionFree.FourPrimeHighDigitTailOrder
import GRHArticle.ProgressionFree.RankinHighDigitMaskMass

/-!
# The four-prime high-digit charge bound

The exact greedy low masses are those of one or two ternary digits.
Combining them with the geometric high-mass bound recovers the article's
coefficient for the bad-high contribution.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

private theorem rankinLowExponents_one : rankinLowExponents 1 = {0,1} := by
  ext n
  simp only [mem_rankinLowExponents,mem_insert,mem_singleton,Nat.pow_one]
  constructor
  · rintro ⟨hn,h⟩
    have hrem := ((mem_greedyExponents_iff n).mp h).1
    rw [Nat.mod_eq_of_lt hn] at hrem
    omega
  · rintro (rfl | rfl)
    · exact ⟨by decide,zero_mem_greedyExponents⟩
    · exact ⟨by decide,one_mem_greedyExponents⟩

private theorem three_mem_greedyExponents : 3 ∈ greedyExponents :=
  (mem_greedyExponents_iff 3).mpr ⟨by decide,one_mem_greedyExponents⟩

private theorem four_mem_greedyExponents_for_tail : 4 ∈ greedyExponents :=
  (mem_greedyExponents_iff 4).mpr ⟨by decide,one_mem_greedyExponents⟩

private theorem rankinLowExponents_two : rankinLowExponents 2 = {0,1,3,4} := by
  ext n
  simp only [mem_rankinLowExponents,mem_insert,mem_singleton,show (3:ℕ)^2=9 by decide]
  constructor
  · rintro ⟨hn,h⟩
    have h₀ := (mem_greedyExponents_iff n).mp h
    have h₁ := ((mem_greedyExponents_iff (n/3)).mp h₀.2).1
    omega
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨by decide,zero_mem_greedyExponents⟩
    · exact ⟨by decide,one_mem_greedyExponents⟩
    · exact ⟨by decide,three_mem_greedyExponents⟩
    · exact ⟨by decide,four_mem_greedyExponents_for_tail⟩

private theorem sum_rankinLowExponents_fourPrime (u : ℝ) (i : Fin 4) :
    (∑ a ∈ rankinLowExponents (fourPrimeLowDigitDepth i), u^a) =
      ∏ j ∈ range (fourPrimeLowDigitDepth i), (1+u^(3^j)) := by
  have hi : fourPrimeLowDigitDepth i = 1 ∨ fourPrimeLowDigitDepth i = 2 := by
    fin_cases i <;> decide
  rcases hi with h | h
  · rw [h,rankinLowExponents_one]
    simp
  · rw [h,rankinLowExponents_two]
    norm_num [Finset.sum_insert,Finset.prod_range_succ]
    ring

/-- The article's explicit high-digit factor bounds the admitted bad-high
mass in any progression-free rule on four prime coordinates. -/
theorem reciprocalExponentMass_fourPrimeBadHigh_le (q : Fin 4 → ℚ)
    (hq : ∀ i, 1 < q i) {F : Set (Fin 4 → ℕ)} (hF : ThreeAPFree F) :
    let u := fun i ↦ 1 / (q i : ℝ)
    reciprocalExponentMass u (rankinBadHighVectors fourPrimeLowDigitDepth F) ≤
      reciprocalExponentMass u (rankinExponentVectors (Fin 4) \ F) *
        (fourPrimeHighDigitTail q : ℝ) := by
  let u (i : Fin 4) : ℝ := 1/(q i : ℝ)
  have hq' (i : Fin 4) : 1 < (q i : ℝ) := by exact_mod_cast hq i
  have hq₀ (i : Fin 4) : 0 < (q i : ℝ) := zero_lt_one.trans (hq' i)
  have hu (i : Fin 4) : 0 ≤ u i := div_nonneg zero_le_one (hq₀ i).le
  have hu₁ (i : Fin 4) : u i < 1 := (div_lt_one (hq₀ i)).mpr (hq' i)
  dsimp only
  refine (reciprocalExponentMass_rankinBadHigh_le u hu hu₁ fourPrimeLowDigitDepth hF).trans ?_
  apply mul_le_mul_of_nonneg_left _
    (by
      rw [reciprocalExponentMass_eq_tsum_subtype]
      exact tsum_nonneg (fun _ ↦ reciprocalExponentWeight_nonneg hu _))
  unfold fourPrimeHighDigitTail
  push_cast
  apply sum_le_sum
  intro e _
  have h := reciprocalExponentMass_rankinHighDigitMasks_le
    (fun i ↦ u i^(e.val+1)) (fun i ↦ pow_nonneg (hu i) _)
    (fun i ↦ pow_lt_one₀ (hu i) (hu₁ i) (by omega)) fourPrimeLowDigitDepth
  simp_rw [sum_rankinLowExponents_fourPrime,←pow_mul,u,div_pow,one_pow] at h
  simpa only [u,div_pow,one_pow] using h

end GRHArticle.ProgressionFree
