import FabiusFunction.StirlingCompleteHomogeneous
import FabiusFunction.StirlingFirstModH
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# The symmetric-function descriptions of both Stirling triangles

The two Stirling triangles are evaluations of the two fundamental symmetric
families:

* `S(k+r,k) = h_r(1,2,...,k)`;
* `c(n,n-r) = e_r(0,1,...,n-1)` for `r ≤ n`.

Both identities hold after casting into every commutative semiring. The
second-kind identity is imported from `StirlingCompleteHomogeneous`, which
identifies the generating series over the integers and transports the result
to every commutative semiring. The first-kind proof reads the coefficients
of the rising factorial using Vieta's formula.

The resulting identities require no division, characteristic-zero hypothesis,
or distinctness of the variable values. Scaling all variables gives the
homogeneous versions of both identities.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

noncomputable section

variable {R : Type*} [CommSemiring R]

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
