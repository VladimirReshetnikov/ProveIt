import FabiusFunction.CompleteHomogeneous
import FabiusFunction.StirlingFirstModH
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The symmetric-function descriptions of both Stirling triangles

The two Stirling triangles are evaluations of the two fundamental symmetric
families:

* `S(k+r,k) = h_r(1,2,...,k)`;
* `c(n,n-r) = e_r(0,1,...,n-1)` for `r ≤ n`.

Both identities hold after casting into every commutative semiring. The
second-kind proof compares the adjoining-variable recurrence of complete
homogeneous functions with the Stirling recurrence. The first-kind proof
reads the coefficients of the rising factorial using Vieta's formula.

In particular, the complete homogeneous formula does not require subtraction,
formal reciprocals, characteristic zero, or distinct values of the variables.
Scaling all variables gives the homogeneous versions of both identities.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

noncomputable section

variable {R : Type*} [CommSemiring R]

/-- Second-kind Stirling numbers are complete homogeneous symmetric functions
of `1, ..., k`, over every commutative semiring. The shifted indices include
the empty family and its degree-zero value without exceptional conventions. -/
theorem stirlingSecond_add_eq_completeHomogeneousEvalOn (k r : ℕ) :
    (Nat.stirlingSecond (k + r) k : R) =
      completeHomogeneousEvalOn (Finset.range k) (fun j => ((j + 1 : ℕ) : R)) r := by
  induction k generalizing r with
  | zero =>
      cases r with
      | zero => simp [completeHomogeneousEvalOn]
      | succ r => simp [completeHomogeneousEvalOn, Nat.stirlingSecond_succ_zero]
  | succ k ih =>
      induction r with
      | zero => simp [completeHomogeneousEvalOn, Nat.stirlingSecond_self]
      | succ r ihr =>
          have hrec := completeHomogeneousEvalOn_insert_succ
            (Finset.notMem_range_self (n := k))
            (fun j => ((j + 1 : ℕ) : R)) r
          rw [← Finset.range_succ] at hrec
          rw [hrec, ← ihr, ← ih (r + 1)]
          rw [show k + 1 + (r + 1) = (k + r + 1) + 1 by omega,
            show k + 1 + r = k + r + 1 by omega,
            show k + (r + 1) = k + r + 1 by omega,
            Nat.stirlingSecond_succ_succ, Nat.cast_add, Nat.cast_mul]

/-- The complete homogeneous description in the usual unshifted indices.
The hypothesis `k ≤ n` is necessary because natural subtraction truncates. -/
theorem stirlingSecond_eq_completeHomogeneousEvalOn (n k : ℕ) (h : k ≤ n) :
    (Nat.stirlingSecond n k : R) =
      completeHomogeneousEvalOn (Finset.range k) (fun j => ((j + 1 : ℕ) : R))
        (n - k) := by
  simpa only [Nat.add_sub_of_le h] using
    (stirlingSecond_add_eq_completeHomogeneousEvalOn (R := R) k (n - k))

/-- Scaling `1, ..., k` by an arbitrary scalar multiplies the degree-`r`
complete homogeneous evaluation by that scalar to the power `r`. No
nonzeroness or cancellation hypothesis is needed. -/
theorem completeHomogeneousEvalOn_scaled_range (a : R) (k r : ℕ) :
    completeHomogeneousEvalOn (Finset.range k)
        (fun j => a * ((j + 1 : ℕ) : R)) r =
      a ^ r * (Nat.stirlingSecond (k + r) k : R) := by
  rw [stirlingSecond_add_eq_completeHomogeneousEvalOn]
  exact completeHomogeneousEval_smul a
    (fun j : Finset.range k => ((j.1 + 1 : ℕ) : R)) r

/-- The elementary-symmetric description of first-kind Stirling numbers,
written as the sum of products over subsets of the variable indices. -/
theorem stirlingFirst_eq_sum_powersetCard (n r : ℕ) (h : r ≤ n) :
    (Nat.stirlingFirst n (n - r) : R) =
      ∑ s ∈ (Finset.range n).powersetCard r, ∏ i ∈ s, (i : R) := by
  have hcoeff := Finset.prod_X_add_C_coeff (Finset.range n)
    (fun i => (i : R)) (k := n - r)
    (by simpa only [Finset.card_range] using Nat.sub_le n r)
  rw [← ascPochhammer_eq_prod_range R n, coeff_ascPochhammer,
    if_pos (Nat.sub_le n r)] at hcoeff
  simpa only [Finset.card_range, Nat.sub_sub_self h] using hcoeff

/-- First-kind Stirling numbers are the elementary symmetric functions of
`0, ..., n-1`, with Mathlib's multiset evaluation retaining repeated values
after passage to positive characteristic. -/
theorem stirlingFirst_eq_esymm (n r : ℕ) (h : r ≤ n) :
    (Nat.stirlingFirst n (n - r) : R) =
      ((Finset.range n).val.map (fun i => (i : R))).esymm r := by
  rw [Finset.esymm_map_val]
  exact stirlingFirst_eq_sum_powersetCard n r h

/-- The homogeneous first-kind formula remains valid when all variables are
scaled, including a zero or nilpotent scale. -/
theorem esymm_scaled_range (a : R) (n r : ℕ) (h : r ≤ n) :
    ((Finset.range n).val.map (fun i => a * (i : R))).esymm r =
      a ^ r * (Nat.stirlingFirst n (n - r) : R) := by
  rw [stirlingFirst_eq_esymm n r h]
  simpa only [smul_eq_mul, Multiset.map_map, Function.comp_apply] using
    (Multiset.pow_smul_esymm a r
      ((Finset.range n).val.map (fun i => (i : R)))).symm

end

end Fabius
