import GRHArticle.ProgressionFree.PolynomialCounterexample
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Product over ternary digit positions for the greedy generating function

The finite identity holds over any commutative semiring. Over a complete
normed field it yields an unconditionally convergent product for every
argument in the open unit ball.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology
open scoped Classical BigOperators

private theorem greedy_digit_mem (n r : ℕ) (hr : r < 3) :
    3*n+r ∈ greedyExponents ↔ r ≤ 1 ∧ n ∈ greedyExponents := by
  rw [mem_greedyExponents_iff]
  have h₁ : (3*n+r)%3 = r := by omega
  have h₂ : (3*n+r)/3 = n := by omega
  rw [h₁,h₂]

private theorem sum_greedy_triple_prefix {R : Type*} [CommSemiring R] (x : R) (N : ℕ) :
    ∑ a ∈ Finset.range (3*N), greedyExponents.indicator (x^·) a =
      (1+x) * ∑ n ∈ Finset.range N, greedyExponents.indicator ((x^3)^·) n := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hd (r : ℕ) (hr : r < 3) : greedyExponents.indicator (x^·) (3*N+r) =
        if r ≤ 1 ∧ N ∈ greedyExponents then x^(3*N+r) else 0 := by
      simp only [Set.indicator, greedy_digit_mem N r hr]
    have h0 := hd 0 (by decide)
    have h1 := hd 1 (by decide)
    have h2 := hd 2 (by decide)
    rw [show 3*(N+1) = (3*N+2)+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ (n := 3*N+1), Finset.sum_range_succ (n := 3*N),
      ih, Finset.sum_range_succ (n := N)]
    by_cases h : N ∈ greedyExponents <;>
      simp [h, Set.indicator] at h0 h1 h2 <;>
      simp_all [Set.indicator, pow_succ x (3*N), pow_mul, add_mul, mul_add]
    ring

/-- Prefixes of length `3^k` have an exact factor for each ternary digit. -/
theorem greedyExponent_digitProduct_prefix {R : Type*} [CommSemiring R] (x : R) (k : ℕ) :
    ∑ a ∈ Finset.range (3^k), greedyExponents.indicator (x^·) a =
      ∏ j ∈ Finset.range k, (1+x^(3^j)) := by
  induction k generalizing x with
  | zero => simp [zero_mem_greedyExponents]
  | succ k ih =>
    rw [pow_succ' 3 k, sum_greedy_triple_prefix, ih, Finset.prod_range_succ']
    simp only [pow_zero, pow_one, ← pow_mul, ← pow_succ' 3]
    ring

/-- The digit product defines the greedy exponent series throughout the open
unit ball of any complete normed field, including complex arguments. -/
theorem hasProd_greedyExponent_digits {K : Type*} [NormedField K] [CompleteSpace K]
    {x : K} (hx : ‖x‖ < 1) :
    HasProd (fun j : ℕ ↦ 1+x^(3^j)) (∑' n : ℕ, greedyExponents.indicator (x^·) n) := by
  have hg := summable_geometric_of_norm_lt_one hx
  have hn := summable_geometric_of_lt_one (norm_nonneg x) hx
  have hs : Summable (fun j : ℕ ↦ ‖x^(3^j)‖) := by
    simpa [Function.comp_def] using hn.comp_injective (Nat.pow_right_injective (by decide : 2 ≤ 3))
  apply (multipliable_one_add_of_summable hs).hasProd_iff_tendsto_nat.mpr
  have ht := (hg.indicator greedyExponents).hasSum.tendsto_sum_nat.comp
    (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (3:ℕ)))
  exact ht.congr fun k ↦ greedyExponent_digitProduct_prefix x k

/-- The degree benchmark is the product over the positive ternary digit
positions after the first factor cancels with the geometric normalizer. -/
theorem polynomialDegreeBenchmark_eq_digitProduct (F : Type*) [Field F] [Fintype F] :
    let z := (Fintype.card F : ℝ)⁻¹
    polynomialDegreeBenchmark F = (1-z^2) * ∏' j : ℕ, (1+z^(3^(j+1))) := by
  let z := (Fintype.card F : ℝ)⁻¹
  have hq : (1:ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hz : ‖z‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [z]; positivity)]
    exact inv_lt_one_of_one_lt₀ hq
  have h := hasProd_greedyExponent_digits hz
  change (1-z) * (∑' d : ℕ, greedyExponents.indicator (z^·) d) =
    (1-z^2) * ∏' j : ℕ, (1+z^(3^(j+1)))
  have hs : (∑' n : ℕ, greedyExponents.indicator (z^·) n) =
      (1+z) * ∏' j : ℕ, (1+z^(3^(j+1))) := by
    calc
      _ = ∏' j : ℕ, (1+z^(3^j)) := h.tprod_eq.symm
      _ = _ := by
        have h₃ : ‖z^3‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hz (by decide)
        have htail := (hasProd_greedyExponent_digits h₃).multipliable
        have htail' : Multipliable (fun n : ℕ ↦ 1 + z^(3^(n+1))) := by
          simpa only [← pow_mul, ← pow_succ' 3] using htail
        simpa only [pow_zero, pow_one] using
          (tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 + z^(3^n)) htail')
  rw [hs, ← mul_assoc]
  congr 1
  ring

end GRHArticle.ProgressionFree
