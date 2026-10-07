/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open Polynomial
open scoped BigOperators

theorem coeff_X_sub_C_mul_abs_le (p : ℝ[X]) {M y : ℝ} (hM : 0 ≤ M)
    (hp : ∀ n, |p.coeff n| ≤ M) (hy : |y| ≤ 1) (n : ℕ) :
    |((X - C y) * p).coeff n| ≤ 2 * M := by
  cases n with
  | zero =>
    simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_mul, abs_neg,
      abs_mul]
    calc
      |y| * |p.coeff 0| ≤ 1 * M := mul_le_mul hy (hp 0) (abs_nonneg _) zero_le_one
      _ ≤ 2 * M := by linarith
  | succ n =>
    rw [coeff_X_sub_C_mul]
    calc
      |p.coeff n - y * p.coeff (n + 1)| ≤ |p.coeff n| + |y * p.coeff (n + 1)| := abs_sub _ _
      _ = |p.coeff n| + |y| * |p.coeff (n + 1)| := by rw [abs_mul]
      _ ≤ M + 1 * M := add_le_add (hp n) (mul_le_mul hy (hp (n + 1)) (abs_nonneg _) zero_le_one)
      _ = 2 * M := by ring

theorem coeff_prod_X_sub_C_abs_le {ι : Type*} (s : Finset ι) (v : ι → ℝ)
    (hv : ∀ i ∈ s, |v i| ≤ 1) (n : ℕ) :
    |(∏ i ∈ s, (X - C (v i))).coeff n| ≤ (2 : ℝ) ^ s.card := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, coeff_one]
    split_ifs <;> norm_num
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ]
    have hp (k : ℕ) : |(∏ j ∈ s, (X - C (v j))).coeff k| ≤ (2 : ℝ) ^ s.card := by
      exact ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)) k
    simpa only [mul_comm] using coeff_X_sub_C_mul_abs_le (∏ j ∈ s, (X - C (v j)))
      (by positivity : 0 ≤ (2 : ℝ) ^ s.card) hp (hv i (Finset.mem_insert_self i s)) n

theorem lagrange_basis_coeff_abs_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ) (i : ι) {r : ℝ} (hr : 0 < r)
    (hv : ∀ j ∈ s, |v j| ≤ 1)
    (hsep : ∀ j ∈ s.erase i, r ≤ |v i - v j|) (n : ℕ) :
    |(Lagrange.basis s v i).coeff n| ≤ (2 / r) ^ (s.erase i).card := by
  have heq : Lagrange.basis s v i =
      C (∏ j ∈ s.erase i, (v i - v j)⁻¹) * ∏ j ∈ s.erase i, (X - C (v j)) := by
    simp only [Lagrange.basis, Lagrange.basisDivisor, Finset.prod_mul_distrib, map_prod]
  have hprod : (∏ j ∈ s.erase i, |(v i - v j)⁻¹|) ≤ (r⁻¹) ^ (s.erase i).card := by
    apply (Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) (fun j hj => ?_)).trans_eq
      (Finset.prod_const _)
    rw [abs_inv]
    simpa only [one_div] using one_div_le_one_div_of_le hr (hsep j hj)
  rw [heq, coeff_C_mul, abs_mul, Finset.abs_prod]
  calc
    _ ≤ (r⁻¹) ^ (s.erase i).card * (2 : ℝ) ^ (s.erase i).card :=
      mul_le_mul hprod (coeff_prod_X_sub_C_abs_le (s.erase i) v
        (fun j hj => hv j (Finset.mem_of_mem_erase hj)) n) (abs_nonneg _) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped BigOperators

theorem polynomial_coeff_le_of_separated_samples (p : ℝ[X]) (t : Finset ℝ)
    {r u : ℝ} (hr : 0 < r) (hu : 0 ≤ u) (hdeg : p.degree < t.card)
    (ht : ∀ x ∈ t, |x| ≤ 1) (hval : ∀ x ∈ t, |p.eval x| ≤ u)
    (hsep : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → r ≤ |x - y|) (n : ℕ) :
    |p.coeff n| ≤ (t.card : ℝ) * u * (2 / r) ^ (t.card - 1) := by
  classical
  have heq : p = Lagrange.interpolate t id (fun x => p.eval x) :=
    Lagrange.eq_interpolate (fun _ _ _ _ h => h) hdeg
  have hterm (x : ℝ) (hx : x ∈ t) :
      |(C (p.eval x) * Lagrange.basis t id x).coeff n| ≤ u * (2 / r) ^ (t.card - 1) := by
    rw [coeff_C_mul, abs_mul]
    apply mul_le_mul (hval x hx) _ (abs_nonneg _) hu
    have h := lagrange_basis_coeff_abs_le t id x hr ht
      (fun y hy => hsep x hx y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm) n
    simpa only [Finset.card_erase_of_mem hx] using h
  calc
    |p.coeff n| = |(∑ x ∈ t, C (p.eval x) * Lagrange.basis t id x).coeff n| :=
      congrArg (fun q : ℝ[X] => |q.coeff n|) heq
    _ = |∑ x ∈ t, (C (p.eval x) * Lagrange.basis t id x).coeff n| := by rw [finsetSum_coeff]
    _ ≤ ∑ x ∈ t, |(C (p.eval x) * Lagrange.basis t id x).coeff n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ t, u * (2 / r) ^ (t.card - 1) := Finset.sum_le_sum hterm
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end Erdos3

end

end OAI
