import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Integer certificates from coprime moduli

For a finite family of pairwise coprime integer moduli, simultaneous
congruences imply divisibility by their product. A strict bound by the
absolute product then certifies zero, or equality after taking a difference.
Half-product bounds are a convenient symmetric specialization when bounding
representatives separately; they are unnecessarily restrictive for a zero test.

The moduli may be signed or composite, and the index set may be empty.
The size hypotheses themselves rule out a zero product. No reconstruction
algorithm or primality assumption is used.
-/

set_option autoImplicit false

open scoped BigOperators Function

namespace Fabius

variable {ι : Type*}

/-- Simultaneous zero congruences for pairwise coprime integer moduli imply
divisibility by the product, including an empty family of moduli. -/
theorem int_prod_dvd_of_pairwise_coprime
    (s : Finset ι) (m : ι → ℤ) (N : ℤ)
    (hcop : (s : Set ι).Pairwise (IsCoprime on m))
    (hzero : ∀ i ∈ s, N ≡ 0 [ZMOD m i]) : (∏ i ∈ s, m i) ∣ N :=
  Finset.prod_dvd_of_coprime hcop
    (fun i hi => Int.modEq_zero_iff_dvd.mp (hzero i hi))

/-- A zero congruence certificate is exact under the sharp strict bound
`|N| < |∏ mᵢ|`; a half-product bound is not required. -/
theorem int_eq_zero_of_modEq_zero_of_natAbs_lt_prod
    (s : Finset ι) (m : ι → ℤ) (N : ℤ)
    (hcop : (s : Set ι).Pairwise (IsCoprime on m))
    (hzero : ∀ i ∈ s, N ≡ 0 [ZMOD m i])
    (hbound : N.natAbs < (∏ i ∈ s, m i).natAbs) : N = 0 :=
  Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (int_prod_dvd_of_pairwise_coprime s m N hcop hzero) hbound

/-- Congruent integers are equal when the absolute value of their difference
is smaller than the absolute product of pairwise coprime moduli. -/
theorem int_eq_of_modEq_of_natAbs_sub_lt_prod
    (s : Finset ι) (m : ι → ℤ) (a b : ℤ)
    (hcop : (s : Set ι).Pairwise (IsCoprime on m))
    (hmod : ∀ i ∈ s, a ≡ b [ZMOD m i])
    (hbound : (b - a).natAbs < (∏ i ∈ s, m i).natAbs) : a = b := by
  have hdiv : (∏ i ∈ s, m i) ∣ b - a :=
    Finset.prod_dvd_of_coprime hcop (fun i hi => (hmod i hi).dvd)
  exact (sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv hbound)).symm

/-- Separate magnitude bounds give an equality certificate when their sum
is smaller than the absolute product of the coprime moduli. -/
theorem int_eq_of_modEq_of_natAbs_add_lt_prod
    (s : Finset ι) (m : ι → ℤ) (a b : ℤ)
    (hcop : (s : Set ι).Pairwise (IsCoprime on m))
    (hmod : ∀ i ∈ s, a ≡ b [ZMOD m i])
    (hbound : b.natAbs + a.natAbs < (∏ i ∈ s, m i).natAbs) : a = b :=
  int_eq_of_modEq_of_natAbs_sub_lt_prod s m a b hcop hmod
    ((Int.natAbs_sub_le b a).trans_lt hbound)

/-- Two representatives strictly inside the symmetric half-product interval
with matching residues are equal, without integer division conventions. -/
theorem int_eq_of_modEq_of_two_mul_natAbs_lt_prod
    (s : Finset ι) (m : ι → ℤ) (a b : ℤ)
    (hcop : (s : Set ι).Pairwise (IsCoprime on m))
    (hmod : ∀ i ∈ s, a ≡ b [ZMOD m i])
    (ha : 2 * a.natAbs < (∏ i ∈ s, m i).natAbs)
    (hb : 2 * b.natAbs < (∏ i ∈ s, m i).natAbs) : a = b := by
  apply int_eq_of_modEq_of_natAbs_add_lt_prod s m a b hcop hmod
  omega

end Fabius

