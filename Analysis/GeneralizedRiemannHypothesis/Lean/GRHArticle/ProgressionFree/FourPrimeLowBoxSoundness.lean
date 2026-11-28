import GRHArticle.ProgressionFree.FourPrimeLowBoxData
import Mathlib.Tactic.Positivity

/-!
# Soundness of the four-prime low-box calculation

An increasing multiplicative midpoint relation at the base primes gives an
additive midpoint relation on all four exponent coordinates. Thus the finite
branch check bounds every progression-free subset of the box. Clearing
the exact denominator recovers the real weighted inequality.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

private theorem sum_map_filter {α M : Type*} [AddMonoid M]
    (L : List α) (test : α → Bool) (w : α → M) :
    ((L.filter test).map w).sum = (L.map fun a ↦ if test a then w a else 0).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => cases h : test a <;> simp [h,ih]

private theorem sum_map_fourPrimeSortedExponents {M : Type*} [AddCommMonoid M]
    (q r : Fin 4 → ℕ) (w : (Fin 4 → ℕ) → M) :
    ((fourPrimeSortedExponents q r).map w).sum = ∑ a ∈ exponentBox r, w a := by
  change (Multiset.map w (fourPrimeSortedExponents q r : Multiset _)).sum = _
  rw [fourPrimeSortedExponents_coe]
  rfl

/-- The target equals the integer score of the greedy subset. -/
theorem fourPrimeBoxTarget_eq_sum (q r : Fin 4 → ℕ) :
    fourPrimeBoxTarget q r =
      ∑ a ∈ exponentBox r, if fourPrimeBoxGood a then fourPrimeBoxScore q a else 0 := by
  unfold fourPrimeBoxTarget
  rw [sum_map_filter]
  simp only [fourPrimeBoxEntries,List.map_map,Function.comp_def]
  exact sum_map_fourPrimeSortedExponents q r _

/-- If a base prefix passes the checker, its greedy vectors bound the
inflated integer score of every progression-free subset. -/
theorem fourPrimeBoxScore_le_of_check
    (q r : Fin 4 → ℕ) (hq : ∀ i, (q i).Prime) (hInj : Function.Injective q)
    (hc : fourPrimeBoxCheck q r = true)
    (F : Set (Fin 4 → ℕ)) (hF : ThreeAPFree F) :
    letI : DecidablePred (· ∈ F) := fun _ ↦ Classical.propDecidable _
    (∑ a ∈ exponentBox r, if a ∈ F then fourPrimeBoxScore q a else 0) ≤
      ∑ a ∈ exponentBox r, if fourPrimeBoxGood a then fourPrimeBoxScore q a else 0 := by
  classical
  let test (a : FourPrimeBoxEntry) := decide (a.1 ∈ F ∧ a.2.1 = fourPrimeBoxValue q a.1)
  have hFree (a b c : FourPrimeBoxEntry) (ha : test a = true) (hb : test b = true)
      (h₁ : test c = true) : fourPrimeBoxForbidden a b c = false := by
    have ha' := of_decide_eq_true ha
    have hb' := of_decide_eq_true hb
    have hc' := of_decide_eq_true h₁
    apply Bool.eq_false_of_not_eq_true
    intro h
    have ⟨hab,_,he⟩ := of_decide_eq_true h
    rw [ha'.2,hb'.2] at hab
    rw [ha'.2,hb'.2,hc'.2] at he
    have hMid : a.1+c.1 = b.1+b.1 := by
      funext i
      have hi := (mul_eq_mul_iff_prime_exponents (fourPrimeBoxValue_pos q a.1 hq).ne'
        (fourPrimeBoxValue_pos q b.1 hq).ne' (fourPrimeBoxValue_pos q c.1 hq).ne').mp he (q i) (hq i)
      simpa only [Pi.add_apply,fourPrimeBoxValue_factorization q _ hq hInj i] using hi
    rw [hF ha'.1 hb'.1 hc'.1 hMid] at hab
    exact (lt_irrefl _) hab
  let L := fourPrimeBoxEntries q r
  have h := finiteGPBranchCheck_sound (fun a : FourPrimeBoxEntry ↦ a.2.2) fourPrimeBoxForbidden
    (fourPrimeBoxTarget q r) test hFree (L.length+1) L hc
  unfold fourPrimeBoxTarget at h
  rw [sum_map_filter,sum_map_filter] at h
  dsimp only [L,fourPrimeBoxEntries] at h
  simp only [List.map_map,Function.comp_def,test,and_true,decide_eq_true_eq] at h
  rw [sum_map_fourPrimeSortedExponents,sum_map_fourPrimeSortedExponents] at h
  exact h

private theorem cast_fourPrimeBoxScore (q a : Fin 4 → ℕ) (hq : ∀ i, (q i).Prime)
    (ha : ∀ i, a i ≤ fourPrimeLowBoxLimit i) :
    (fourPrimeBoxScore q a : ℝ) =
      ((20:ℝ) * ∏ i, (q i : ℝ)^(fourPrimeLowBoxLimit i)) *
        ((if fourPrimeBoxGood a then 1 else 21/20) * ∏ i, (1/(q i : ℝ))^(a i)) := by
  let D : ℝ := ∏ i, (q i : ℝ)^(fourPrimeLowBoxLimit i)
  let V : ℝ := ∏ i, (q i : ℝ)^(a i)
  have hV : 0 < V := prod_pos fun i _ ↦ pow_pos (by exact_mod_cast (hq i).pos) _
  have hInv : (∏ i, (1/(q i : ℝ))^(a i)) = V⁻¹ := by
    simp only [V,one_div,inv_pow,prod_inv_distrib]
  have hNumerator : (fourPrimeBoxWeightNumerator q a : ℝ) = D * V⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq₀ hV.ne').2
    rw [fourPrimeBoxWeightNumerator_eq_prod]
    unfold D V
    push_cast
    rw [←prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    rw [←pow_add,Nat.sub_add_cancel (ha i)]
  rw [fourPrimeBoxScore,Nat.cast_mul,hNumerator,hInv]
  change _ = 20*D*_
  cases fourPrimeBoxGood a <;> simp <;> ring

/-- A bound on the inflated integer score gives the identical inequality
with real reciprocal weights. -/
theorem fourPrimeBoxWeighted_le_of_integerScore
    (q r : Fin 4 → ℕ) (hq : ∀ i, (q i).Prime) (hr : ∀ i, r i ≤ fourPrimeLowBoxLimit i)
    (F : Set (Fin 4 → ℕ))
    (h : letI : DecidablePred (· ∈ F) := fun _ ↦ Classical.propDecidable _
      (∑ a ∈ exponentBox r, if a ∈ F then fourPrimeBoxScore q a else 0) ≤ fourPrimeBoxTarget q r) :
    letI : DecidablePred (· ∈ F) := fun _ ↦ Classical.propDecidable _
    (∑ a ∈ exponentBox r, if a ∈ F then (if fourPrimeBoxGood a then 1 else (21:ℝ)/20) *
        ∏ i, (1/(q i : ℝ))^(a i) else 0) ≤
      ∑ a ∈ exponentBox r, if fourPrimeBoxGood a then ∏ i, (1/(q i : ℝ))^(a i) else 0 := by
  classical
  let C := (20:ℝ) * ∏ i, (q i : ℝ)^(fourPrimeLowBoxLimit i)
  have hC : 0 < C := mul_pos (by norm_num)
    (prod_pos fun i _ ↦ pow_pos (by exact_mod_cast (hq i).pos) _)
  rw [fourPrimeBoxTarget_eq_sum] at h
  have hCast :
      (∑ a ∈ exponentBox r, if a ∈ F then (fourPrimeBoxScore q a : ℝ) else 0) ≤
        ∑ a ∈ exponentBox r, if fourPrimeBoxGood a then (fourPrimeBoxScore q a : ℝ) else 0 := by
    exact_mod_cast h
  apply (mul_le_mul_iff_of_pos_left hC).mp
  rw [mul_sum,mul_sum]
  refine le_trans (le_of_eq ?_) (hCast.trans (le_of_eq ?_))
  · apply sum_congr rfl
    intro a ha
    have he := cast_fourPrimeBoxScore q a hq (fun i ↦ (mem_exponentBox.mp ha i).trans (hr i))
    by_cases h : a ∈ F <;> simp [h,he,C]
  · apply sum_congr rfl
    intro a ha
    have he := cast_fourPrimeBoxScore q a hq (fun i ↦ (mem_exponentBox.mp ha i).trans (hr i))
    cases h : fourPrimeBoxGood a <;> simp [h,he,C]

/-- The checked bound on a rectangular prefix, with real reciprocal weights. -/
theorem fourPrimeBoxWeighted_le_of_check
    (q r : Fin 4 → ℕ) (hq : ∀ i, (q i).Prime) (hInj : Function.Injective q)
    (hr : ∀ i, r i ≤ fourPrimeLowBoxLimit i) (hc : fourPrimeBoxCheck q r = true)
    (F : Set (Fin 4 → ℕ)) (hF : ThreeAPFree F) :
    letI : DecidablePred (· ∈ F) := fun _ ↦ Classical.propDecidable _
    (∑ a ∈ exponentBox r, if a ∈ F then (if fourPrimeBoxGood a then 1 else (21:ℝ)/20) *
        ∏ i, (1/(q i : ℝ))^(a i) else 0) ≤
      ∑ a ∈ exponentBox r, if fourPrimeBoxGood a then ∏ i, (1/(q i : ℝ))^(a i) else 0 :=
  fourPrimeBoxWeighted_le_of_integerScore q r hq hr F
    ((fourPrimeBoxScore_le_of_check q r hq hInj hc F hF).trans_eq (fourPrimeBoxTarget_eq_sum q r).symm)

end GRHArticle.ProgressionFree
