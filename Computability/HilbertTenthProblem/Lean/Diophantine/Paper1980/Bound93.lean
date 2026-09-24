import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Size bounds for the coefficients of `D · C²`

If every coefficient of `Q` is nonnegative then `|[X^p](P · Q)| ≤ D₁ · Q(1)`
where `D₁ = Σ_d |[X^d] P|` (`abs_coeff_mul_le`).  For the digit polynomial
`C` with nonnegative digits this gives `|a_p| ≤ D₁ · C(1)²`, the bound `A_C`
of Section 4 of the affine-radix proof (there with `D₁` absorbed into the
choice of `H₀`).  The geometric tail estimate `tail_le` turns it into the
smallness of the part of `Σ a_p B^p` below a window.
-/

namespace Jones1980

namespace Iso

open Polynomial

/-- `D₁ = Σ_d |[X^d] P|`. -/
noncomputable def absSum (P : ℤ[X]) : ℤ := ∑ d ∈ P.support, |P.coeff d|

theorem absSum_nonneg (P : ℤ[X]) : 0 ≤ absSum P :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- A coefficient of a polynomial with nonnegative coefficients is at most its value at `1`. -/
theorem coeff_le_eval_one {Q : ℤ[X]} (hQ : ∀ w, 0 ≤ Q.coeff w) (w : ℕ) :
    Q.coeff w ≤ Q.eval 1 := by
  rw [eval_eq_sum]
  simp only [one_pow, mul_one]
  by_cases hw : w ∈ Q.support
  · exact Finset.single_le_sum (fun i _ => hQ i) hw
  · rw [Polynomial.notMem_support_iff.1 hw]
    exact Finset.sum_nonneg fun i _ => hQ i

theorem eval_one_nonneg {Q : ℤ[X]} (hQ : ∀ w, 0 ≤ Q.coeff w) : 0 ≤ Q.eval 1 := by
  rw [eval_eq_sum]; simp only [one_pow, mul_one]
  exact Finset.sum_nonneg fun i _ => hQ i

/-- `|[X^p](P · Q)| ≤ D₁(P) · Q(1)` when `Q` has nonnegative coefficients. -/
theorem abs_coeff_mul_le (P Q : ℤ[X]) (hQ : ∀ w, 0 ≤ Q.coeff w) (p : ℕ) :
    |(P * Q).coeff p| ≤ absSum P * Q.eval 1 := by
  rw [coeff_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hQ1 := eval_one_nonneg hQ
  -- each term is bounded by `|P_d| · Q(1)`; the sum over the antidiagonal is a sum over `d`
  calc ∑ ij ∈ Finset.antidiagonal p, |P.coeff ij.1 * Q.coeff ij.2|
      ≤ ∑ ij ∈ Finset.antidiagonal p, |P.coeff ij.1| * Q.eval 1 := by
        apply Finset.sum_le_sum
        intro ij _
        rw [abs_mul, abs_of_nonneg (hQ _)]
        exact mul_le_mul_of_nonneg_left (coeff_le_eval_one hQ _) (abs_nonneg _)
    _ = (∑ d ∈ Finset.range (p + 1), |P.coeff d|) * Q.eval 1 := by
        rw [Finset.sum_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ ≤ absSum P * Q.eval 1 := by
        apply mul_le_mul_of_nonneg_right _ hQ1
        unfold absSum
        -- restrict to the support
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (p + 1)) (fun d => d ∈ P.support)]
        have h0 : ∑ d ∈ (Finset.range (p + 1)).filter (fun d => d ∉ P.support), |P.coeff d| = 0 := by
          apply Finset.sum_eq_zero
          intro d hd
          rw [Finset.mem_filter] at hd
          rw [Polynomial.notMem_support_iff.1 hd.2, abs_zero]
        rw [h0, add_zero]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hd; exact (Finset.mem_filter.1 hd).2
        · intro d _ _; exact abs_nonneg _

/-- The geometric tail: `|Σ_{p < N} a_p B^p| ≤ K · 2 · B^(N−1)` for `|a_p| ≤ K`, `B ≥ 2`, `N ≥ 1`. -/
theorem tail_le {B N : ℕ} (hB : 2 ≤ B) (hN : 1 ≤ N) {a : ℕ → ℤ} {K : ℤ}
    (ha : ∀ p, |a p| ≤ K) :
    |∑ p ∈ Finset.range N, a p * (B : ℤ) ^ p| ≤ K * (2 * (B : ℤ) ^ (N - 1)) := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (ha 0)
  have hBZ : (2 : ℤ) ≤ B := by exact_mod_cast hB
  -- `Σ_{p<N} B^p ≤ 2 B^(N−1)`
  have hgeom : ∀ n, 1 ≤ n → ∑ p ∈ Finset.range n, (B : ℤ) ^ p ≤ 2 * (B : ℤ) ^ (n - 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      rw [Finset.sum_range_succ]
      have e : (B : ℤ) ^ (n + 1 - 1) = B ^ (n - 1) * B := by
        rw [Nat.add_sub_cancel, ← pow_succ]; congr 1; omega
      have hp : (0 : ℤ) < B ^ (n - 1) := by positivity
      rw [e]
      have h2 : (B : ℤ) ^ n = B ^ (n - 1) * B := by rw [← pow_succ]; congr 1; omega
      rw [h2]
      nlinarith
  calc |∑ p ∈ Finset.range N, a p * (B : ℤ) ^ p|
      ≤ ∑ p ∈ Finset.range N, |a p * (B : ℤ) ^ p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Finset.range N, K * (B : ℤ) ^ p := by
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (B : ℤ) ^ p)]
        exact mul_le_mul_of_nonneg_right (ha p) (by positivity)
    _ = K * ∑ p ∈ Finset.range N, (B : ℤ) ^ p := by rw [Finset.mul_sum]
    _ ≤ K * (2 * (B : ℤ) ^ (N - 1)) := mul_le_mul_of_nonneg_left (hgeom N hN) hK

end Iso

end Jones1980
