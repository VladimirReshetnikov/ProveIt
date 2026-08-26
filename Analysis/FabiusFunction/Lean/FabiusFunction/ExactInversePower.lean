import FabiusFunction.NormalizedEvenMoments
import FabiusFunction.NormalizedMoments

/-!
# Exact inverse-power formulas

Arithmetic proofs of equations (16), (25), and (26) from
*Arithmetic of the Fabius function*.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- Equation (16), derived entirely from the exact half-moment formulas. -/
theorem fabiusAtInverseTwoPow_odd_formula (n : ℕ) :
    fabiusAtInverseTwoPow (2 * n + 1) =
      (momentNumerator n : ℚ) /
        ((2 : ℚ) ^ (2 * n + 1).choose 2 * 2 * Nat.factorial (2 * n) *
          oddDoubleFactorial (n + 1) * evenMersenneProduct n) := by
  rw [fabiusAtInverseTwoPow_eq_halfMoment, halfMomentFabiusValue,
    halfMoment_odd_eq_moment, moment_eq_momentNumerator_div]
  rw [show 2 * n + 1 = 2 * n + 1 by rfl, Nat.factorial_succ]
  push_cast
  field_simp

/-- Equation (25), expressing an inverse-power value through `G_n`. -/
theorem fabiusAtInverseTwoPow_eq_halfMomentNumerator_formula (n : ℕ) :
    fabiusAtInverseTwoPow n =
      (halfMomentNumerator n : ℚ) /
        ((2 : ℚ) ^ n.choose 2 * n.factorial * (n + 1).factorial *
          mersenneProduct n) := by
  rw [fabiusAtInverseTwoPow_eq_halfMoment, halfMomentFabiusValue,
    halfMoment_eq_halfMomentNumerator]
  push_cast
  ring

/-- Split the first `2n+1` Mersenne factors into their even- and odd-indexed
subproducts. -/
theorem mersenneProduct_split_odd_even (n : ℕ) :
    mersenneProduct (2 * n + 1) =
      evenMersenneProduct n * oddMersenneProduct n := by
  induction n with
  | zero => norm_num [mersenneProduct, evenMersenneProduct, oddMersenneProduct]
  | succ n ih =>
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega,
        mersenneProduct_succ_eq, mersenneProduct_succ_eq, ih,
        evenMersenneProduct_succ_eq, oddMersenneProduct_succ_eq]
      ring_nf

/-- Division-free natural-number form of Equation (26). -/
theorem halfMomentNumerator_odd_index_eq (n : ℕ) :
    halfMomentNumerator (2 * n + 1) =
      (2 * n + 1) *
        (2 ^ n * (n + 1).factorial * momentNumerator n *
          oddMersenneProduct n) := by
  have hfac :
      (2 * n + 2).factorial =
        2 ^ (n + 1) * (n + 1).factorial * oddDoubleFactorial (n + 1) := by
    simpa [show 2 * (n + 1) = 2 * n + 2 by omega] using
      factorial_two_mul_eq (n + 1)
  have hhalf := halfMoment_eq_halfMomentNumerator (2 * n + 1)
  rw [halfMoment_odd_eq_moment, moment_eq_momentNumerator_div] at hhalf
  rw [show 2 * n + 1 + 1 = 2 * n + 2 by omega, hfac,
    mersenneProduct_split_odd_even] at hhalf
  have hoddPos : 0 < oddDoubleFactorial (n + 1) :=
    oddDoubleFactorial_pos (n + 1)
  have hevenPos : 0 < evenMersenneProduct n := evenMersenneProduct_pos n
  have hoddMerPos : 0 < oddMersenneProduct n := oddMersenneProduct_pos n
  have hoddNz : ((oddDoubleFactorial (n + 1) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hoddPos
  have hevenNz : ((evenMersenneProduct n : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hevenPos
  have hoddMerNz : ((oddMersenneProduct n : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hoddMerPos
  have hEq :
      (halfMomentNumerator (2 * n + 1) : ℚ) / (2 * n + 1) =
        ((2 ^ n * (n + 1).factorial * momentNumerator n *
          oddMersenneProduct n : ℕ) : ℚ) := by
    field_simp [hoddNz, hevenNz, hoddMerNz] at hhalf ⊢
    push_cast at hhalf ⊢
    rw [pow_succ] at hhalf
    apply mul_left_cancel₀ (a :=
      2 * (oddDoubleFactorial (n + 1) : ℚ) * (evenMersenneProduct n : ℚ))
    · positivity
    · linear_combination -hhalf
  let R : ℕ :=
    2 ^ n * (n + 1).factorial * momentNumerator n * oddMersenneProduct n
  have hcast :
      (halfMomentNumerator (2 * n + 1) : ℚ) =
        ((2 * n + 1 : ℕ) : ℚ) * (R : ℚ) := by
    calc
      (halfMomentNumerator (2 * n + 1) : ℚ) =
          ((halfMomentNumerator (2 * n + 1) : ℚ) / (2 * n + 1)) *
            (2 * n + 1) := by field_simp
      _ = (R : ℚ) * (2 * n + 1) := by
        have hh := congrArg
          (fun q : ℚ => q * (((2 * n + 1 : ℕ) : ℚ))) hEq
        simpa [R] using hh
      _ = ((2 * n + 1 : ℕ) : ℚ) * (R : ℚ) := by
        push_cast
        ring
  have hnat : halfMomentNumerator (2 * n + 1) = (2 * n + 1) * R := by
    exact_mod_cast hcast
  simpa only [R] using hnat

/-- Equation (26), together with its natural divisibility consequence. -/
theorem halfMomentNumerator_odd_index_formula (n : ℕ) :
    (halfMomentNumerator (2 * n + 1) : ℚ) / (2 * n + 1) =
      ((2 ^ n * (n + 1).factorial * momentNumerator n *
        oddMersenneProduct n : ℕ) : ℚ) ∧
    (2 * n + 1) * momentNumerator n ∣ halfMomentNumerator (2 * n + 1) := by
  rw [halfMomentNumerator_odd_index_eq]
  constructor
  · push_cast
    field_simp
  · refine ⟨2 ^ n * (n + 1).factorial * oddMersenneProduct n, ?_⟩
    ring

end Fabius
