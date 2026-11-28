import GRHArticle.ProgressionFree.FourPrimeLowBoxSoundness
import GRHArticle.ProgressionFree.FourPrimeOptimalityFromBoxes

/-!
# Transport checked low boxes to larger prime tuples

The finite checks are performed only for rectangular prefixes of a fixed
base tuple. Positive prefix coefficients transport the deficit inequality
to all primes above that base. The full high-digit argument then applies.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

/-- The base-prefix checks give the low-box deficit at all larger weights. -/
theorem fourPrimeLowBox_deficit_of_checkedPrefixes
    (b : Fin 4 → ℕ) (hb : ∀ i, (b i).Prime) (hDistinct : Function.Injective b)
    (q : Fin 4 → ℚ) (hBQ : ∀ i, (b i:ℚ) ≤ q i)
    (fixed : Finset (Fin 4)) (hFixed : ∀ i ∈ fixed, (b i:ℚ) = q i)
    (hCheck : ∀ r ∈ exponentBox fourPrimeLowBoxLimit,
      (∀ i ∈ fixed, r i = fourPrimeLowBoxLimit i) → fourPrimeBoxCheck b r = true)
    (A : Set (Fin 4 → ℕ)) (hA : ThreeAPFree A) :
    let u := fun i ↦ 1/(q i:ℝ)
    (21:ℝ)/20 * exponentDigitSliceMass u fourPrimeLowDigitDepth (A \ rankinExponentVectors _) 0 ≤
      exponentDigitSliceMass u fourPrimeLowDigitDepth (rankinExponentVectors _ \ A) 0 := by
  classical
  let G := rankinExponentVectors (Fin 4)
  let u (i : Fin 4) : ℝ := 1/(q i:ℝ)
  let s (a : Fin 4 → ℕ) : ℝ := if a ∈ A then (if fourPrimeBoxGood a then 1 else 21/20) else 0
  let g (a : Fin 4 → ℕ) : ℝ := if fourPrimeBoxGood a then 1 else 0
  let c (a : Fin 4 → ℕ) : ℝ := s a-g a
  let L := exponentBox fourPrimeLowBoxLimit
  have hPrefix (r : Fin 4 → ℕ) (hr : r ∈ L)
      (hR : ∀ i ∈ fixed, r i = fourPrimeLowBoxLimit i) :
      (∑ a ∈ exponentBox r, c a * ∏ i, (1/(b i:ℝ))^(a i)) ≤ 0 := by
    have h := fourPrimeBoxWeighted_le_of_check b r hb hDistinct (mem_exponentBox.mp hr)
      (hCheck r hr hR) A hA
    simp only [c,sub_mul,sum_sub_distrib]
    apply sub_nonpos.mpr
    simpa only [s,g,ite_mul,zero_mul,one_mul] using h
  have hTransport := sum_mul_reciprocal_pow_prod_le_zero_of_exponentBox_prefixes
    fourPrimeLowBoxLimit fixed c (fun i ↦ (b i:ℝ)) (fun i ↦ (q i:ℝ))
    (fun i ↦ by exact_mod_cast (hb i).pos)
    (fun i ↦ by exact_mod_cast hBQ i) (fun i hi ↦ by exact_mod_cast hFixed i hi)
    hPrefix
  let w := reciprocalExponentWeight u
  have he (a : Fin 4 → ℕ) : c a * w a =
      21/20 * (if a ∈ A \ G then w a else 0) - (if a ∈ G \ A then w a else 0) := by
    have hGood : fourPrimeBoxGood a = true ↔ a ∈ G := fourPrimeBoxGood_iff a
    by_cases ha : a ∈ A <;> by_cases hg : a ∈ G
    · have h := hGood.mpr hg
      simp [c,s,g,ha,hg,h,Set.mem_sdiff]
    · have h := Bool.eq_false_of_not_eq_true (fun ht ↦ hg (hGood.mp ht))
      simp [c,s,g,ha,hg,h,Set.mem_sdiff]
    · have h := hGood.mpr hg
      simp [c,s,g,ha,hg,h,Set.mem_sdiff]
    · have h := Bool.eq_false_of_not_eq_true (fun ht ↦ hg (hGood.mp ht))
      simp [c,s,g,ha,hg,h,Set.mem_sdiff]
  have hJ (a : Fin 4 → ℕ) : joinExponentDigits fourPrimeLowDigitDepth a 0 = a := by
    funext i
    simp [joinExponentDigits]
  unfold exponentDigitSliceMass
  simp_rw [hJ]
  apply sub_nonpos.mp
  change (21:ℝ)/20 * (∑ a ∈ L, if a ∈ A \ G then w a else 0) -
    (∑ a ∈ L, if a ∈ G \ A then w a else 0) ≤ 0
  rw [mul_sum,←sum_sub_distrib]
  have h : (∑ a ∈ L, c a*w a) ≤ 0 := by
    simpa only [L,w,reciprocalExponentWeight,u] using hTransport
  simpa only [←he] using h

/-- Rankin is optimal on every tuple covered by the checked prefixes and
a certified high-digit margin at its base tuple. -/
theorem reciprocalExponentMass_fourPrimeRankinOptimal_of_checkedPrefixes
    (b : Fin 4 → ℕ) (hb : ∀ i, (b i).Prime) (hDistinct : Function.Injective b)
    (q : Fin 4 → ℚ) (hBQ : ∀ i, (b i:ℚ) ≤ q i)
    (fixed : Finset (Fin 4)) (hFixed : ∀ i ∈ fixed, (b i:ℚ) = q i)
    (hCheck : ∀ r ∈ exponentBox fourPrimeLowBoxLimit,
      (∀ i ∈ fixed, r i = fourPrimeLowBoxLimit i) → fourPrimeBoxCheck b r = true)
    (hMargin : (20:ℚ)/21 + fourPrimeHighDigitTail (fun i ↦ (b i:ℚ)) ≤ 1)
    {F : Set (Fin 4 → ℕ)} (hF : ThreeAPFree F) :
    let u := fun i ↦ 1/(q i:ℝ)
    reciprocalExponentMass u F ≤ reciprocalExponentMass u (rankinExponentVectors (Fin 4)) := by
  have hPrime (i : Fin 4) : 1 < (b i:ℚ) := by exact_mod_cast (hb i).one_lt
  have hq (i : Fin 4) : 1 < q i := (hPrime i).trans_le (hBQ i)
  have hTail := fourPrimeHighDigitTail_le_of_le hPrime hBQ
  have hm : (20:ℚ)/21 + fourPrimeHighDigitTail q ≤ 1 := by linarith
  exact reciprocalExponentMass_fourPrimeRankinOptimal_of_boxes q hq hm hF
    (fourPrimeLowBox_deficit_of_checkedPrefixes b hb hDistinct q hBQ fixed hFixed hCheck)

end GRHArticle.ProgressionFree
