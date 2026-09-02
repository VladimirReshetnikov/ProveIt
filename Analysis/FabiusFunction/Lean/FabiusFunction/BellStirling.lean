import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Exponential
import FabiusFunction.StirlingBasisChange

/-!
# Bell numbers, Touchard polynomials, and Dobiński's formula

Mathlib's `Nat.bell` is defined by the binomial recurrence
`B(n+1) = ∑_k C(n,k) B(k)`.  This module connects it with the second-kind
Stirling triangle and with the Poisson moment series.

* The *vertical* recurrence `S(n+1,k+1) = ∑_{i ≤ n} C(n,i) S(i,k)` (the block
  containing the last element is chosen first), proved by induction from the
  ordinary recurrence and Pascal's rule.
* `B(n) = ∑_k S(n,k)`, because the right-hand side satisfies Mathlib's
  binomial recurrence.  With the surjection formula this is the double sum
  `B(n) = ∑_k (1/k!) ∑_i (-1)^(k-i) C(k,i) i^n`.
* The Touchard polynomials `T_n(X) = ∑_k S(n,k) X^k`, with `T_n(1) = B(n)`
  and the binomial-type recurrence `T_{n+1} = X ∑_k C(n,k) T_k`.
* The Poisson moment identity
  `∑_m m^n λ^m / m! = e^λ ∑_k S(n,k) λ^k` for every real `λ`, from the
  falling-factorial expansion of `m^n` and the exponential series shifted by
  `k` places; Dobiński's formula `B(n) = e^{-1} ∑_m m^n/m!` is the case
  `λ = 1`.  (Read probabilistically: the `n`-th moment of a Poisson variable
  of mean `λ` is the Touchard polynomial `T_n(λ)`.)

## Main results

* `stirlingSecond_succ_succ_eq_sum`, `bell_eq_sum_stirlingSecond`,
  `bell_eq_sum_sum_div_factorial`.
* `touchardPolynomial`, `touchardPolynomial_eval_one`,
  `touchardPolynomial_succ`.
* `hasSum_descFactorial_mul_pow_div_factorial`,
  `tsum_pow_mul_pow_div_factorial`, `dobinski`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-! ### The vertical recurrence and the Bell numbers -/

/-- **Vertical recurrence for the second kind:**
`S(n+1,k+1) = ∑_{i ≤ n} C(n,i) S(i,k)`. -/
theorem stirlingSecond_succ_succ_eq_sum (n k : ℕ) :
    Nat.stirlingSecond (n + 1) (k + 1) =
      ∑ i ∈ Finset.range (n + 1), n.choose i * Nat.stirlingSecond i k := by
  induction n generalizing k with
  | zero => simp [Nat.stirlingSecond_succ_succ]
  | succ n ih =>
    have h := Finset.sum_choose_succ_mul (R := ℕ) (fun i _ => Nat.stirlingSecond i k) n
    simp only [Nat.cast_id] at h
    rw [h, ← ih k]
    cases k with
    | zero =>
      simp [Nat.stirlingSecond_succ_zero, Nat.stirlingSecond_one_right]
    | succ k' =>
      have hsplit : ∑ i ∈ Finset.range (n + 1), n.choose i * Nat.stirlingSecond (i + 1) (k' + 1)
          = (k' + 1) * ∑ i ∈ Finset.range (n + 1), n.choose i * Nat.stirlingSecond i (k' + 1)
            + ∑ i ∈ Finset.range (n + 1), n.choose i * Nat.stirlingSecond i k' := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Nat.stirlingSecond_succ_succ]
        ring
      rw [hsplit, ← ih (k' + 1), ← ih k', Nat.stirlingSecond_succ_succ]
      ring

/-- **Stirling decomposition of the Bell numbers:** `B(n) = ∑_{k ≤ n} S(n,k)`. -/
theorem bell_eq_sum_stirlingSecond (n : ℕ) :
    Nat.bell n = ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hrefl : (∑ i ∈ Finset.range (n + 1), n.choose i * Nat.bell (n - i))
          = ∑ i ∈ Finset.range (n + 1), n.choose i * Nat.bell i := by
        rw [← Finset.sum_range_reflect (fun i => n.choose i * Nat.bell i) (n + 1)]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hsub : n + 1 - 1 - i = n - i := by omega
        simp only [hsub, Nat.choose_symm hi']
      have hext : ∀ i ∈ Finset.range (n + 1),
          (∑ k ∈ Finset.range (i + 1), Nat.stirlingSecond i k) =
            ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond i k := by
        intro i hi
        have hi' : i < n + 1 := Finset.mem_range.mp hi
        apply Finset.sum_subset (Finset.range_mono (show i + 1 ≤ n + 1 by omega))
        intro k _ hk
        have hik : i < k := by
          rw [Finset.mem_range, not_lt] at hk
          omega
        exact Nat.stirlingSecond_eq_zero_of_lt hik
      rw [Nat.bell_succ, ← Nat.range_succ_eq_Iic, hrefl]
      conv_rhs => rw [Finset.sum_range_succ', Nat.stirlingSecond_succ_zero, add_zero]
      calc ∑ i ∈ Finset.range (n + 1), n.choose i * Nat.bell i
          = ∑ i ∈ Finset.range (n + 1),
              n.choose i * ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond i k := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [ih i (Finset.mem_range.mp hi), hext i hi]
        _ = ∑ k ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
              n.choose i * Nat.stirlingSecond i k := by
            simp_rw [Finset.mul_sum]
            exact Finset.sum_comm
        _ = ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond (n + 1) (k + 1) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [stirlingSecond_succ_succ_eq_sum]

/-- The Bell number as the inclusion–exclusion double sum
`B(n) = ∑_{k ≤ n} (1/k!) ∑_{i ≤ k} (-1)^(k-i) C(k,i) i^n`. -/
theorem bell_eq_sum_sum_div_factorial (n : ℕ) :
    (Nat.bell n : ℚ) = ∑ k ∈ Finset.range (n + 1),
      (∑ i ∈ Finset.range (k + 1), (-1 : ℚ) ^ (k - i) * k.choose i * (i : ℚ) ^ n) /
        k.factorial := by
  rw [bell_eq_sum_stirlingSecond]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  exact stirlingSecond_eq_sum_div_factorial n k

/-! ### Touchard polynomials -/

/-- The Touchard (exponential) polynomials `T_n(X) = ∑_{k ≤ n} S(n,k) X^k`. -/
noncomputable def touchardPolynomial (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : R[X]) * X ^ k

/-- `T_n(1) = B(n)`. -/
theorem touchardPolynomial_eval_one (R : Type*) [CommRing R] (n : ℕ) :
    (touchardPolynomial R n).eval 1 = Nat.bell n := by
  rw [bell_eq_sum_stirlingSecond, touchardPolynomial, eval_finsetSum]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

/-- The binomial-type recurrence of the Touchard polynomials:
`T_{n+1}(X) = X · ∑_{k ≤ n} C(n,k) T_k(X)`. -/
theorem touchardPolynomial_succ (R : Type*) [CommRing R] (n : ℕ) :
    touchardPolynomial R (n + 1) =
      X * ∑ k ∈ Finset.range (n + 1), (n.choose k : R[X]) * touchardPolynomial R k := by
  simp only [touchardPolynomial]
  rw [sum_mul_sum_mul_eq (fun k => (n.choose k : R[X]))
    (fun k j => (Nat.stirlingSecond k j : R[X])) (fun j => (X : R[X]) ^ j) n
    (fun k j hkj => by simp [Nat.stirlingSecond_eq_zero_of_lt hkj])]
  rw [Finset.sum_range_succ', Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul, add_zero,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [stirlingSecond_succ_succ_eq_sum]
  push_cast
  ring

/-! ### Poisson moments and Dobiński's formula -/

/-- The falling-factorial moment series of the Poisson weights:
`∑_m m^{\underline k} λ^m / m! = λ^k e^λ`. -/
theorem hasSum_descFactorial_mul_pow_div_factorial (l : ℝ) (k : ℕ) :
    HasSum (fun m : ℕ => (m.descFactorial k : ℝ) * l ^ m / m.factorial) (l ^ k * Real.exp l) := by
  have hexp : HasSum (fun j : ℕ => l ^ j / j.factorial) (Real.exp l) := by
    have h := NormedSpace.expSeries_div_hasSum_exp l
    rwa [← Real.exp_eq_exp_ℝ] at h
  have hshift : (fun j : ℕ => ((j + k).descFactorial k : ℝ) * l ^ (j + k) / (j + k).factorial)
      = fun j : ℕ => l ^ k * (l ^ j / j.factorial) := by
    funext j
    have hfac : (j.factorial : ℝ) * ((j + k).descFactorial k : ℝ) = ((j + k).factorial : ℝ) := by
      have := Nat.factorial_mul_descFactorial (show k ≤ j + k by omega)
      rw [Nat.add_sub_cancel] at this
      exact_mod_cast this
    have hD : (((j + k).descFactorial k : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.not.mpr (show ¬ j + k < k by omega)
    rw [← hfac, pow_add, mul_comm (((j + k).descFactorial k : ℕ) : ℝ), mul_div_mul_right _ _ hD]
    ring
  have hzero : (∑ i ∈ Finset.range k, ((i.descFactorial k : ℝ) * l ^ i / i.factorial)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp hi), Nat.cast_zero, zero_mul,
      zero_div]
  have hmain := (hasSum_nat_add_iff' k).mp
    (by
      rw [hzero, sub_zero]
      show HasSum (fun j : ℕ => ((j + k).descFactorial k : ℝ) * l ^ (j + k) / (j + k).factorial)
        (l ^ k * Real.exp l)
      rw [hshift]
      exact hexp.mul_left (l ^ k))
  exact hmain

/-- **The Poisson moment identity:** for every real `λ` and every `n`,
`∑_m m^n λ^m / m! = e^λ ∑_{k ≤ n} S(n,k) λ^k`. -/
theorem tsum_pow_mul_pow_div_factorial (l : ℝ) (n : ℕ) :
    ∑' m : ℕ, (m : ℝ) ^ n * l ^ m / m.factorial =
      Real.exp l * ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : ℝ) * l ^ k := by
  have hterm : ∀ m : ℕ, (m : ℝ) ^ n * l ^ m / m.factorial =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.stirlingSecond n k : ℝ) * ((m.descFactorial k : ℝ) * l ^ m / m.factorial) := by
    intro m
    have h : ((m : ℝ)) ^ n = ∑ k ∈ Finset.range (n + 1),
        (Nat.stirlingSecond n k : ℝ) * (m.descFactorial k : ℝ) := by
      have h0 := congrArg (Nat.cast : ℕ → ℝ) (pow_eq_sum_stirlingSecond_mul_descFactorial m n)
      push_cast at h0
      exact h0
    rw [h, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hsum : HasSum (fun m : ℕ => (m : ℝ) ^ n * l ^ m / m.factorial)
      (∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : ℝ) * (l ^ k * Real.exp l)) := by
    have hfun : (fun m : ℕ => (m : ℝ) ^ n * l ^ m / m.factorial)
        = fun m : ℕ => ∑ k ∈ Finset.range (n + 1),
            (Nat.stirlingSecond n k : ℝ) * ((m.descFactorial k : ℝ) * l ^ m / m.factorial) :=
      funext hterm
    rw [hfun]
    exact hasSum_sum (fun k _ => (hasSum_descFactorial_mul_pow_div_factorial l k).mul_left _)
  rw [hsum.tsum_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Dobiński's formula:** `B(n) = e^{-1} ∑_m m^n / m!`, stated as
`∑_m m^n / m! = e · B(n)`. -/
theorem dobinski (n : ℕ) :
    ∑' m : ℕ, (m : ℝ) ^ n / m.factorial = Real.exp 1 * Nat.bell n := by
  have h := tsum_pow_mul_pow_div_factorial 1 n
  simp only [one_pow, mul_one] at h
  rw [h, bell_eq_sum_stirlingSecond, Nat.cast_sum]

end Fabius
