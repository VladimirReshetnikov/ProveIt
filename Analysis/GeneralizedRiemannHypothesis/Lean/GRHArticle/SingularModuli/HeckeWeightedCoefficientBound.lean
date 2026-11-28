import GRHArticle.SingularModuli.HeckePackedPolynomialArithmetic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A degree-sensitive packing bound for powers of nonnegative polynomials

Evaluating the input at one half bounds its low-degree coefficients after
raising it to a power. This avoids sizing each digit by the sum of all
coefficients of the full power.
-/

namespace GRHArticle.SingularModuli

open Polynomial

/-- The numerator used to check the dyadic evaluation bound by integer arithmetic. -/
def dyadicScaledEvaluation (l : List ℕ) : ℕ :=
  2 * l.foldl (fun s a ↦ 2*s+a) 0

private noncomputable abbrev toRat (P : ℕ[X]) : ℚ[X] := P.map (Nat.castRingHom ℚ)

private theorem dyadic_fold_eval (l : List ℕ) (z : ℕ) :
    (↑(l.foldl (fun s a ↦ 2*s+a) z) : ℚ) =
      2^l.length * ((z : ℚ) + (toRat (coefficientListPolynomial l)).eval (1/2) / 2) := by
  induction l generalizing z with
  | nil => simp [coefficientListPolynomial]
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, coefficientListPolynomial, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.coe_castRingHom, pow_succ]
    ring

private theorem dyadic_eval_le_of_le (l : List ℕ) (w : ℕ)
    (h : dyadicScaledEvaluation l ≤ 2^(l.length+w)) :
    (toRat (coefficientListPolynomial l)).eval (1/2) ≤ 2^w := by
  let s : ℕ := l.foldl (fun x a ↦ 2*x+a) 0
  have hg : (s : ℚ) =
      2^l.length * ((0 : ℚ) + (toRat (coefficientListPolynomial l)).eval (1/2) / 2) :=
    dyadic_fold_eval l 0
  change 2 * s ≤ 2^(l.length+w) at h
  have hk : (2 : ℚ) * (s : ℚ) ≤ (2 : ℚ)^(l.length+w) := by exact_mod_cast h
  rw [hg, pow_add] at hk
  simp only [zero_add] at hk
  apply le_of_mul_le_mul_left _ (show (0:ℚ) < 2^l.length by positivity)
  calc
    _ = 2 * (2^l.length * ((toRat (coefficientListPolynomial l)).eval (1/2)/2)) := by ring
    _ ≤ _ := hk

private theorem coeff_mul_pow_le_eval {P : ℚ[X]} (hn : ∀ i, 0 ≤ P.coeff i) (i : ℕ)
    {r : ℚ} (hr : 0 ≤ r) : P.coeff i * r^i ≤ P.eval r := by
  by_cases hi : i ≤ P.natDegree
  · rw [Polynomial.eval_eq_sum_range]
    exact Finset.single_le_sum (fun j _ ↦ mul_nonneg (hn j) (pow_nonneg hr _))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hi), zero_mul, Polynomial.eval_eq_sum_range]
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg (hn j) (pow_nonneg hr _)

/-- A certified dyadic evaluation bounds the coefficient at each degree `i`. -/
theorem coeff_pow_le_of_dyadicScaledEvaluation_le (l : List ℕ) (w k i : ℕ)
    (h : dyadicScaledEvaluation l ≤ 2^(l.length+w)) :
    (coefficientListPolynomial l ^ k).coeff i ≤ 2^(w*k+i) := by
  let P := coefficientListPolynomial l
  let Q := toRat P
  let r : ℚ := 1/2
  have hn (j : ℕ) : 0 ≤ (toRat (P^k)).coeff j := by
    rw [Polynomial.coeff_map]
    exact Nat.cast_nonneg _
  have hs := coeff_mul_pow_le_eval hn i (show 0 ≤ r by positivity)
  rw [Polynomial.coeff_map] at hs
  have he : (toRat (P^k)).eval r = Q.eval r ^ k := by
    simp only [toRat, Q, Polynomial.map_pow, Polynomial.eval_pow]
  rw [he] at hs
  change ((P^k).coeff i : ℚ) * r^i ≤ Q.eval r ^ k at hs
  have hq : 0 ≤ Q.eval r := by
    rw [Polynomial.eval_eq_sum_range]
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg
      (by rw [Polynomial.coeff_map]; exact Nat.cast_nonneg _) (pow_nonneg (by positivity) _)
  have hqpow : Q.eval r ^ k ≤ 2^(w*k) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ hq (dyadic_eval_le_of_le l w h) k
  have hm : r^i * (2:ℚ)^i = 1 := by rw [← mul_pow]; norm_num [r]
  have hR : ((P^k).coeff i : ℚ) ≤ (2:ℚ)^(w*k+i) := calc
    _ = (((P^k).coeff i : ℚ) * r^i) * 2^i := by rw [mul_assoc, hm, mul_one]
    _ ≤ (2:ℚ)^(w*k) * 2^i := mul_le_mul_of_nonneg_right (hs.trans hqpow) (by positivity)
    _ = _ := (pow_add ..).symm
  exact_mod_cast hR

/-- Recover coefficients using a smaller digit width when the dyadic check succeeds. -/
theorem packedNaturalPolynomialPowerCoeff_eq_of_dyadicBound (N : ℕ) (l : List ℕ)
    (w k i : ℕ) (h : dyadicScaledEvaluation l ≤ 2^(l.length+w)) (hi : i < N) :
    packedNaturalPolynomialPowerCoeff (packedNaturalPolynomialPowerAtWidth N l k (w*k+N)) i =
      (coefficientListPolynomial l ^ k).coeff i := by
  apply packedNaturalPolynomialPowerCoeff_eq_of_prefixBound N l k _ i hi
  intro j hj
  apply (coeff_pow_le_of_dyadicScaledEvaluation_le l w k j h).trans_lt
  exact Nat.pow_lt_pow_right (by decide) (Nat.add_lt_add_left hj _)

private theorem foldl_ge_two_pow_mul (l : List ℕ) (z : ℕ) :
    2^l.length * z ≤ l.foldl (fun s a ↦ 2*s+a) z := by
  induction l generalizing z with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, pow_succ, mul_assoc, List.foldl_cons]
    exact (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans (ih _)

/-- The dyadic evaluation bound is inherited by every prefix. -/
theorem dyadicScaledEvaluation_le_take (l : List ℕ) (w N : ℕ)
    (h : dyadicScaledEvaluation l ≤ 2^(l.length+w)) :
    dyadicScaledEvaluation (l.take N) ≤ 2^((l.take N).length+w) := by
  let p := l.take N
  let t := l.drop N
  have hc : p ++ t = l := List.take_append_drop _ _
  have hl : p.length+t.length = l.length := by rw [← List.length_append, hc]
  have ht : dyadicScaledEvaluation p * 2^t.length ≤ dyadicScaledEvaluation l := by
    rw [← hc, dyadicScaledEvaluation, dyadicScaledEvaluation, List.foldl_append]
    calc
      (2 * p.foldl (fun s a ↦ 2*s+a) 0) * 2^t.length =
          2 * (2^t.length * p.foldl (fun s a ↦ 2*s+a) 0) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (foldl_ge_two_pow_mul _ _)
  have hh : dyadicScaledEvaluation p * 2^t.length ≤
      2^(p.length+w) * 2^t.length := by
    rw [← pow_add, show p.length+w+t.length = l.length+w by omega]
    exact ht.trans h
  exact Nat.le_of_mul_le_mul_right hh (Nat.two_pow_pos _)

end GRHArticle.SingularModuli
