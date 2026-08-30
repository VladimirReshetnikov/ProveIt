import FabiusFunction.FiniteQBinomialCore

/-!
# Reciprocal symmetry of Gaussian coefficients

The reciprocity underlying palindromicity of the Gaussian polynomial takes
the form most useful for asymptotics at infinity:

`q ^ (k * (n - k)) * gaussianBinomial q⁻¹ n k = gaussianBinomial q n k`.

The principal theorem is proved first for a unit in an arbitrary commutative
semiring.  Thus the argument uses neither a quotient formula nor cancellation
of q-Pochhammer factors and remains valid in semirings with zero divisors.  A
semifield wrapper then exposes the familiar nonzero-parameter statement.  As
a first application, odd-degree Gaussian polynomials vanish at `q = -1` in
every commutative ring; the even-row, odd-column zero is a concrete total
specialization.

## Main results

* `gaussianBinomial_reciprocity_units` is the unit-valued, total reciprocity
  theorem over a commutative semiring.
* `gaussianBinomial_reciprocity` is its semifield-valued wrapper for `q != 0`.
* `gaussianBinomial_neg_one_eq_zero_of_odd_degree` extracts the root at
  `q = -1` in odd degree over every commutative ring.
* `gaussianBinomial_neg_one_even_odd_eq_zero` is the corresponding explicit
  parity specialization.
-/

set_option autoImplicit false

namespace Fabius

private theorem gaussianBinomial_reciprocity_units_of_le
    {R : Type*} [CommSemiring R] (q : Rˣ) {n k : ℕ} (hk : k ≤ n) :
    (q : R) ^ (k * (n - k)) *
        gaussianBinomial ((q⁻¹ : Rˣ) : R) n k =
      gaussianBinomial (q : R) n k := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          have hkn : k ≤ n := Nat.succ_le_succ_iff.mp hk
          by_cases htop : k = n
          · subst k
            simp
          · have hk1n : k + 1 ≤ n := by omega
            have hrow : n + 1 - (k + 1) = n - k := by omega
            have hsub : n - k = (n - (k + 1)) + 1 := by omega
            have hfirst :
                (q : R) ^ ((k + 1) * (n - k)) *
                    ((q⁻¹ : Rˣ) : R) ^ (k + 1) =
                  (q : R) ^ ((k + 1) * (n - (k + 1))) := by
              rw [hsub, Nat.mul_add, Nat.mul_one, pow_add, mul_assoc,
                ← mul_pow]
              simp
            have hexponent :
                (k + 1) * (n - k) =
                  (n - k) + k * (n - k) := by
              calc
                (k + 1) * (n - k) =
                    k * (n - k) + 1 * (n - k) := by
                      rw [Nat.add_mul]
                _ = (n - k) + k * (n - k) := by
                  rw [Nat.one_mul, Nat.add_comm]
            have hsecond :
                (q : R) ^ ((k + 1) * (n - k)) *
                    gaussianBinomial ((q⁻¹ : Rˣ) : R) n k =
                  (q : R) ^ (n - k) *
                    ((q : R) ^ (k * (n - k)) *
                      gaussianBinomial ((q⁻¹ : Rˣ) : R) n k) := by
              rw [hexponent, pow_add, mul_assoc]
            rw [hrow]
            calc
              (q : R) ^ ((k + 1) * (n - k)) *
                    gaussianBinomial ((q⁻¹ : Rˣ) : R)
                      (n + 1) (k + 1) =
                  (q : R) ^ ((k + 1) * (n - k)) *
                      (((q⁻¹ : Rˣ) : R) ^ (k + 1) *
                          gaussianBinomial ((q⁻¹ : Rˣ) : R) n (k + 1) +
                        gaussianBinomial ((q⁻¹ : Rˣ) : R) n k) := by
                rw [gaussianBinomial_succ_succ_alt]
              _ = ((q : R) ^ ((k + 1) * (n - k)) *
                        ((q⁻¹ : Rˣ) : R) ^ (k + 1)) *
                      gaussianBinomial ((q⁻¹ : Rˣ) : R) n (k + 1) +
                    (q : R) ^ ((k + 1) * (n - k)) *
                      gaussianBinomial ((q⁻¹ : Rˣ) : R) n k := by
                ring
              _ = (q : R) ^ ((k + 1) * (n - (k + 1))) *
                      gaussianBinomial ((q⁻¹ : Rˣ) : R) n (k + 1) +
                    (q : R) ^ (n - k) *
                      ((q : R) ^ (k * (n - k)) *
                        gaussianBinomial ((q⁻¹ : Rˣ) : R) n k) := by
                rw [hfirst, hsecond]
              _ = gaussianBinomial (q : R) n (k + 1) +
                    (q : R) ^ (n - k) * gaussianBinomial (q : R) n k := by
                rw [ih hk1n, ih hkn]
              _ = gaussianBinomial (q : R) (n + 1) (k + 1) := by
                rw [gaussianBinomial_succ_succ]

/-- **Reciprocity of Gaussian coefficients, over units.**  For a unit `q`
in any commutative semiring,

`q^(k(n-k)) * [n choose k]_(q⁻¹) = [n choose k]_q`.

The recursive Gaussian coefficient is extended by zero above the diagonal,
so the statement is total in `n` and `k`.  No division, domain hypothesis,
or nonvanishing condition on q-Pochhammer factors is used. -/
theorem gaussianBinomial_reciprocity_units
    {R : Type*} [CommSemiring R] (q : Rˣ) (n k : ℕ) :
    (q : R) ^ (k * (n - k)) *
        gaussianBinomial ((q⁻¹ : Rˣ) : R) n k =
      gaussianBinomial (q : R) n k := by
  by_cases hk : k ≤ n
  · exact gaussianBinomial_reciprocity_units_of_le q hk
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [gaussianBinomial_eq_zero_of_lt ((q⁻¹ : Rˣ) : R) hnk,
      gaussianBinomial_eq_zero_of_lt (q : R) hnk, mul_zero]

/-- **Semifield-valued Gaussian reciprocity.**  For a nonzero semifield element
`q`, the Gaussian coefficient at `q` is its value at the inverse base,
multiplied by the exact degree monomial `q^(k(n-k))`.  The theorem remains
total above the diagonal because both Gaussian coefficients then vanish. -/
theorem gaussianBinomial_reciprocity
    {K : Type*} [Semifield K] (q : K) (hq : q ≠ 0) (n k : ℕ) :
    q ^ (k * (n - k)) * gaussianBinomial q⁻¹ n k =
      gaussianBinomial q n k := by
  simpa only [Units.val_mk0, Units.val_inv_eq_inv_val] using
    gaussianBinomial_reciprocity_units (Units.mk0 q hq) n k

/-- Over the integers, a Gaussian polynomial of odd degree vanishes at
`q = -1`.  This is the universal calculation behind the ring-valued theorem
below. -/
private theorem gaussianBinomial_neg_one_eq_zero_of_odd_degree_int
    (n k : ℕ) (hdegree : Odd (k * (n - k))) :
    gaussianBinomial (-1 : ℤ) n k = 0 := by
  have hreciprocity :
      -gaussianBinomial (-1 : ℤ) n k = gaussianBinomial (-1 : ℤ) n k := by
    simpa only [Units.coe_neg_one, inv_neg, inv_one, hdegree.neg_one_pow,
      neg_one_mul] using
        gaussianBinomial_reciprocity_units (-1 : ℤˣ) n k
  have hsum :
      gaussianBinomial (-1 : ℤ) n k + gaussianBinomial (-1 : ℤ) n k = 0 := by
    calc
      gaussianBinomial (-1 : ℤ) n k + gaussianBinomial (-1 : ℤ) n k =
          -gaussianBinomial (-1 : ℤ) n k + gaussianBinomial (-1 : ℤ) n k := by
            rw [hreciprocity]
      _ = 0 := neg_add_cancel _
  have hdouble :
      (2 : ℤ) * gaussianBinomial (-1 : ℤ) n k = 0 := by
    simpa [two_mul] using hsum
  exact (mul_eq_zero.mp hdouble).resolve_left (by norm_num)

/-- A Gaussian polynomial of odd degree vanishes at `q = -1` in every
commutative ring.  The proof is universal: establish the integer identity and
transport it along the canonical ring homomorphism, so the result remains
valid in characteristic two as well. -/
theorem gaussianBinomial_neg_one_eq_zero_of_odd_degree
    {R : Type*} [CommRing R] (n k : ℕ) (hdegree : Odd (k * (n - k))) :
    gaussianBinomial (-1 : R) n k = 0 := by
  have hint := gaussianBinomial_neg_one_eq_zero_of_odd_degree_int n k hdegree
  calc
    gaussianBinomial (-1 : R) n k =
        (Int.castRingHom R) (gaussianBinomial (-1 : ℤ) n k) := by
          symm
          simpa using map_gaussianBinomial (Int.castRingHom R) (-1 : ℤ) n k
    _ = 0 := by rw [hint, map_zero]

/-- In an even Gaussian row, every odd column vanishes at `q = -1`:
`[2a choose 2b+1]_(-1) = 0`.  The theorem is total: above the diagonal it
uses the zero extension of the recursive Gaussian coefficient. -/
theorem gaussianBinomial_neg_one_even_odd_eq_zero
    {R : Type*} [CommRing R] (a b : ℕ) :
    gaussianBinomial (-1 : R) (2 * a) (2 * b + 1) = 0 := by
  by_cases hb : b < a
  · apply gaussianBinomial_neg_one_eq_zero_of_odd_degree
    have hsub : 2 * a - (2 * b + 1) = 2 * (a - b - 1) + 1 := by omega
    rw [hsub]
    exact Odd.mul ⟨b, by omega⟩ ⟨a - b - 1, by omega⟩
  · apply gaussianBinomial_eq_zero_of_lt
    omega

end Fabius
