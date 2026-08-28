import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Finite q-binomial algebra over commutative rings

This module isolates the polynomial, denominator-free form of the finite
q-binomial theorem.  The Gaussian coefficient `gaussianBinomial q n k` is
defined by q-Pascal recursion, so it makes sense over every semiring and at
every value of `q`, including roots of unity.  The finite q-Pochhammer product
and its expansion are then proved over an arbitrary commutative ring:

`(z;q)_n = ∑ k≤n, (-1)^k q^(k choose 2) [n choose k]_q z^k`.

This is the reusable algebraic foundation for both the half-base Fabius
formulas and geometric Richardson rows at other bases such as `q = 1/4`.
Quotient formulas belong downstream: they require nonvanishing denominators,
whereas the recursive coefficient and the finite theorem do not.

## Main results

* `gaussianBinomial_succ_succ` and `gaussianBinomial_succ_succ_alt` are the
  two q-Pascal recurrences, both valid for the zero-extended triangle.
* `map_gaussianBinomial` records functoriality under semiring homomorphisms,
  and `gaussianBinomial_symm` gives reflection across the row midpoint
  without division or cancellation.
* `gaussianBinomial_eq_zero_of_lt` and `gaussianBinomial_self` give the two
  triangular boundaries.
* `finiteQPochhammerIn_succ_shift` peels the first product factor.
* `finiteQPochhammerIn_add` splits a product after an arbitrary prefix.
* `finiteQPochhammerIn_self_mul_gaussianBinomial` is the denominator-free
  q-factorial quotient identity.
* `finite_qBinomial_theorem` is the finite product expansion over every
  commutative ring.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

/-- The finite q-Pochhammer product `(a;q)_n` in an arbitrary commutative
ring. -/
def finiteQPochhammerIn {R : Type*} [CommRing R]
    (a q : R) (n : ℕ) : R :=
  ∏ j ∈ Finset.range n, (1 - a * q ^ j)

/-- The empty finite q-Pochhammer product is one. -/
@[simp] theorem finiteQPochhammerIn_zero
    {R : Type*} [CommRing R] (a q : R) :
    finiteQPochhammerIn a q 0 = 1 := by
  simp [finiteQPochhammerIn]

/-- Peeling the last factor of a finite q-Pochhammer product. -/
theorem finiteQPochhammerIn_succ
    {R : Type*} [CommRing R] (a q : R) (n : ℕ) :
    finiteQPochhammerIn a q (n + 1) =
      finiteQPochhammerIn a q n * (1 - a * q ^ n) := by
  simp [finiteQPochhammerIn, Finset.prod_range_succ]

/-- Peeling the first factor of a finite q-Pochhammer product and shifting
the remaining parameter by one power of `q`. -/
theorem finiteQPochhammerIn_succ_shift
    {R : Type*} [CommRing R] (a q : R) (n : ℕ) :
    finiteQPochhammerIn a q (n + 1) =
      (1 - a) * finiteQPochhammerIn (a * q) q n := by
  rw [finiteQPochhammerIn, Finset.prod_range_succ']
  simp only [pow_zero, mul_one]
  calc
    (∏ k ∈ Finset.range n, (1 - a * q ^ (k + 1))) * (1 - a) =
        (1 - a) * ∏ k ∈ Finset.range n, (1 - a * q ^ (k + 1)) :=
      mul_comm _ _
    _ = (1 - a) * ∏ k ∈ Finset.range n, (1 - a * q * q ^ k) := by
      congr 1
      apply Finset.prod_congr rfl
      intro j _hj
      rw [pow_succ']
      ring

/-- **Concatenation of finite q-Pochhammer products.**  Splitting after the
first `m` factors shifts the initial parameter of the remaining `n` factors
by `q ^ m`.

The identity is valid over every commutative ring, including the empty
prefix or suffix and every zero-divisor or positive-characteristic case. -/
theorem finiteQPochhammerIn_add
    {R : Type*} [CommRing R] (a q : R) (m n : ℕ) :
    finiteQPochhammerIn a q (m + n) =
      finiteQPochhammerIn a q m *
        finiteQPochhammerIn (a * q ^ m) q n := by
  unfold finiteQPochhammerIn
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _hj
  rw [pow_add]
  ring

/-- Splitting a self-parameter q-Pochhammer product after its first `m`
factors.  This is the ring-generic form of the usual identity
`(q;q)_(m+n) = (q;q)_m (q^(m+1);q)_n`. -/
theorem finiteQPochhammerIn_self_add
    {R : Type*} [CommRing R] (q : R) (m n : ℕ) :
    finiteQPochhammerIn q q (m + n) =
      finiteQPochhammerIn q q m *
        finiteQPochhammerIn (q ^ (m + 1)) q n := by
  simpa only [pow_succ'] using finiteQPochhammerIn_add q q m n

private theorem finiteQPochhammerIn_pascal_combine
    {R : Type*} [CommRing R] (a q : R) (n : ℕ) :
    finiteQPochhammerIn a q (n + 1) +
        a * (1 - q ^ (n + 1)) * finiteQPochhammerIn (a * q) q n =
      finiteQPochhammerIn (a * q) q (n + 1) := by
  rw [finiteQPochhammerIn_succ_shift, finiteQPochhammerIn_succ]
  rw [show a * q * q ^ n = a * q ^ (n + 1) by rw [pow_succ']; ring]
  ring

/-- The polynomial Gaussian coefficient, extended by zero above the
diagonal.  The recursion is the q-Pascal identity in the orientation suited
to multiplying the finite q-binomial theorem by its next factor. -/
def gaussianBinomial {R : Type*} [Semiring R] (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 =>
      gaussianBinomial q n (k + 1) + q ^ (n - k) * gaussianBinomial q n k

/-- The Gaussian coefficient at the origin is one. -/
@[simp] theorem gaussianBinomial_zero_zero
    {R : Type*} [Semiring R] (q : R) :
    gaussianBinomial q 0 0 = 1 := by
  rfl

/-- Every positive-index Gaussian coefficient in row zero vanishes. -/
@[simp] theorem gaussianBinomial_zero_succ
    {R : Type*} [Semiring R] (q : R) (k : ℕ) :
    gaussianBinomial q 0 (k + 1) = 0 := by
  rfl

/-- The lower edge of every Gaussian row is one. -/
@[simp] theorem gaussianBinomial_zero_right
    {R : Type*} [Semiring R] (q : R) (n : ℕ) :
    gaussianBinomial q n 0 = 1 := by
  cases n <;> rfl

/-- The symmetric q-Pascal recurrence, valid without division or a
nonvanishing hypothesis on `q`. -/
theorem gaussianBinomial_succ_succ
    {R : Type*} [Semiring R] (q : R) (n k : ℕ) :
    gaussianBinomial q (n + 1) (k + 1) =
      gaussianBinomial q n (k + 1) +
        q ^ (n - k) * gaussianBinomial q n k := by
  rfl

/-- Gaussian coefficients commute with every semiring homomorphism.  Thus
all identities proved for the recursive universal coefficient specialize
coefficientwise to quotient rings, finite characteristic, and scalar
extensions. -/
@[simp] theorem map_gaussianBinomial
    {R S : Type*} [Semiring R] [Semiring S]
    (φ : R →+* S) (q : R) (n k : ℕ) :
    φ (gaussianBinomial q n k) = gaussianBinomial (φ q) n k := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [gaussianBinomial_succ_succ,
            gaussianBinomial_succ_succ, map_add, map_mul, map_pow,
            ih (k + 1), ih k]

/-- Gaussian coefficients vanish strictly above the diagonal. -/
theorem gaussianBinomial_eq_zero_of_lt
    {R : Type*} [Semiring R] (q : R) {n k : ℕ} (hk : n < k) :
    gaussianBinomial q n k = 0 := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => exact gaussianBinomial_zero_succ q k
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          rw [gaussianBinomial_succ_succ,
            ih (by omega : n < k + 1), ih (by omega : n < k),
            mul_zero, add_zero]

/-- Every diagonal Gaussian coefficient is one, including row zero. -/
@[simp] theorem gaussianBinomial_self
    {R : Type*} [Semiring R] (q : R) (n : ℕ) :
    gaussianBinomial q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [gaussianBinomial_succ_succ,
        gaussianBinomial_eq_zero_of_lt q (Nat.lt_succ_self n), ih]
      simp

private theorem gaussianBinomial_succ_succ_alt_of_le
    {R : Type*} [CommSemiring R] (q : R) {n k : ℕ} (hk : k ≤ n) :
    gaussianBinomial q (n + 1) (k + 1) =
      q ^ (k + 1) * gaussianBinomial q n (k + 1) +
        gaussianBinomial q n k := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      simp
  | succ n ih =>
      cases k with
      | zero =>
          calc
            gaussianBinomial q (n + 1 + 1) 1 =
                gaussianBinomial q (n + 1) 1 + q ^ (n + 1) := by
              rw [gaussianBinomial_succ_succ]
              simp
            _ = (q * gaussianBinomial q n 1 + 1) +
                q ^ (n + 1) := by
              rw [ih (Nat.zero_le n)]
              simp
            _ = q * (gaussianBinomial q n 1 + q ^ n) + 1 := by
              rw [pow_succ']
              ring
            _ = q * gaussianBinomial q (n + 1) 1 + 1 := by
              rw [gaussianBinomial_succ_succ]
              simp
            _ = q ^ (0 + 1) * gaussianBinomial q (n + 1) (0 + 1) +
                gaussianBinomial q (n + 1) 0 := by
              simp
      | succ k =>
          have hkn : k ≤ n := Nat.succ_le_succ_iff.mp hk
          by_cases hkn' : k = n
          · subst k
            rw [gaussianBinomial_self,
              gaussianBinomial_eq_zero_of_lt q (by omega),
              gaussianBinomial_self]
            simp
          · have hklt : k < n := lt_of_le_of_ne hkn hkn'
            have hk1n : k + 1 ≤ n := by omega
            have hsub : n + 1 - (k + 1) = n - k := by omega
            have hpowLeft :
                q ^ (n - k) * q ^ (k + 1) = q ^ (n + 1) := by
              rw [← pow_add]
              congr 1
              omega
            have hpowRight :
                q ^ (k + 1 + 1) * q ^ (n - (k + 1)) =
                  q ^ (n + 1) := by
              rw [← pow_add]
              congr 1
              omega
            have hleft :
                q ^ (n - k) *
                    (q ^ (k + 1) * gaussianBinomial q n (k + 1)) =
                  q ^ (n + 1) * gaussianBinomial q n (k + 1) := by
              rw [← mul_assoc, hpowLeft]
            have hright :
                q ^ (k + 1 + 1) *
                    (q ^ (n - (k + 1)) *
                      gaussianBinomial q n (k + 1)) =
                  q ^ (n + 1) * gaussianBinomial q n (k + 1) := by
              rw [← mul_assoc, hpowRight]
            calc
              gaussianBinomial q (n + 1 + 1) (k + 1 + 1) =
                  gaussianBinomial q (n + 1) (k + 1 + 1) +
                    q ^ (n - k) *
                      gaussianBinomial q (n + 1) (k + 1) := by
                rw [gaussianBinomial_succ_succ, hsub]
              _ = (q ^ (k + 1 + 1) *
                    gaussianBinomial q n (k + 1 + 1) +
                      gaussianBinomial q n (k + 1)) +
                    q ^ (n - k) *
                      (q ^ (k + 1) *
                          gaussianBinomial q n (k + 1) +
                        gaussianBinomial q n k) := by
                rw [ih hk1n, ih hkn]
              _ = q ^ (k + 1 + 1) *
                    (gaussianBinomial q n (k + 1 + 1) +
                      q ^ (n - (k + 1)) *
                        gaussianBinomial q n (k + 1)) +
                  (gaussianBinomial q n (k + 1) +
                    q ^ (n - k) * gaussianBinomial q n k) := by
                simp only [mul_add, hleft, hright]
                ac_rfl
              _ = q ^ (k + 1 + 1) *
                    gaussianBinomial q (n + 1) (k + 1 + 1) +
                  gaussianBinomial q (n + 1) (k + 1) := by
                rw [← gaussianBinomial_succ_succ,
                  ← gaussianBinomial_succ_succ]

/-- **The second q-Pascal recurrence.**  The zero extension of the Gaussian
triangle makes the identity valid for every pair of natural indices:

`[n+1 choose k+1]_q = q^(k+1) [n choose k+1]_q + [n choose k]_q`.

No admissibility hypothesis, division, cancellation, or nonvanishing
assumption on `q` is needed. -/
theorem gaussianBinomial_succ_succ_alt
    {R : Type*} [CommSemiring R] (q : R) (n k : ℕ) :
    gaussianBinomial q (n + 1) (k + 1) =
      q ^ (k + 1) * gaussianBinomial q n (k + 1) +
        gaussianBinomial q n k := by
  by_cases hk : k ≤ n
  · exact gaussianBinomial_succ_succ_alt_of_le q hk
  · have hnk : n < k := Nat.lt_of_not_ge hk
    rw [gaussianBinomial_eq_zero_of_lt q (by omega : n + 1 < k + 1),
      gaussianBinomial_eq_zero_of_lt q (by omega : n < k + 1),
      gaussianBinomial_eq_zero_of_lt q hnk]
    simp

/-- **Reflection symmetry of recursive Gaussian coefficients.**  For every
commutative semiring and every admissible index,
`[n choose n-k]_q = [n choose k]_q`.

The proof uses the two q-Pascal orientations and never divides or cancels a
q-Pochhammer factor.  It therefore remains valid at `q = 0`, at roots of
unity, in positive characteristic, in the presence of zero divisors, and in
the zero semiring. -/
theorem gaussianBinomial_symm
    {R : Type*} [CommSemiring R] (q : R) {n k : ℕ} (hk : k ≤ n) :
    gaussianBinomial q n (n - k) = gaussianBinomial q n k := by
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
          by_cases hkn' : k = n
          · subst k
            simp
          · have hklt : k < n := lt_of_le_of_ne hkn hkn'
            have hk1n : k + 1 ≤ n := by omega
            have hindex :
                n + 1 - (k + 1) = (n - (k + 1)) + 1 := by
              omega
            rw [hindex,
              gaussianBinomial_succ_succ_alt q n (n - (k + 1))]
            rw [show n - (k + 1) + 1 = n - k by omega,
              ih hkn, ih hk1n, gaussianBinomial_succ_succ]
            ac_rfl

/-- **Denominator-free q-factorial quotient identity.**  Multiplying the
Gaussian coefficient `[n choose k]_q` by `(q;q)_k` selects the final `k`
factors of `(q;q)_n`:

`(q;q)_k [n choose k]_q = (q^(n-k+1);q)_k`.

The theorem holds over every commutative ring, including at `q = 0` and at
roots of unity; no division or regularity assumption is involved. -/
theorem finiteQPochhammerIn_self_mul_gaussianBinomial
    {R : Type*} [CommRing R] (q : R) {n k : ℕ} (hk : k ≤ n) :
    finiteQPochhammerIn q q k * gaussianBinomial q n k =
      finiteQPochhammerIn (q ^ (n - k + 1)) q k := by
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
          by_cases hlt : k < n
          · have hk1n : k + 1 ≤ n := Nat.succ_le_iff.mpr hlt
            have hfirst :
                finiteQPochhammerIn q q (k + 1) *
                    gaussianBinomial q n (k + 1) =
                  finiteQPochhammerIn (q ^ (n - k)) q (k + 1) := by
              simpa only [show n - (k + 1) + 1 = n - k by omega] using
                ih hk1n
            have hsecond :
                finiteQPochhammerIn q q (k + 1) *
                    (q ^ (n - k) * gaussianBinomial q n k) =
                  q ^ (n - k) * (1 - q ^ (k + 1)) *
                    finiteQPochhammerIn (q ^ (n - k + 1)) q k := by
              rw [finiteQPochhammerIn_succ]
              rw [show q * q ^ k = q ^ (k + 1) by rw [pow_succ']]
              calc
                finiteQPochhammerIn q q k * (1 - q ^ (k + 1)) *
                      (q ^ (n - k) * gaussianBinomial q n k) =
                    q ^ (n - k) * (1 - q ^ (k + 1)) *
                      (finiteQPochhammerIn q q k *
                        gaussianBinomial q n k) := by
                  ring
                _ = q ^ (n - k) * (1 - q ^ (k + 1)) *
                      finiteQPochhammerIn (q ^ (n - k + 1)) q k := by
                  rw [ih hkn]
            rw [gaussianBinomial_succ_succ, mul_add]
            calc
              finiteQPochhammerIn q q (k + 1) *
                    gaussianBinomial q n (k + 1) +
                  finiteQPochhammerIn q q (k + 1) *
                    (q ^ (n - k) * gaussianBinomial q n k) =
                  finiteQPochhammerIn (q ^ (n - k)) q (k + 1) +
                    q ^ (n - k) * (1 - q ^ (k + 1)) *
                      finiteQPochhammerIn (q ^ (n - k + 1)) q k := by
                rw [hfirst, hsecond]
              _ = finiteQPochhammerIn (q ^ (n - k + 1)) q (k + 1) := by
                simpa only [show q ^ (n - k) * q =
                    q ^ (n - k + 1) by rw [pow_succ]] using
                  finiteQPochhammerIn_pascal_combine
                    (q ^ (n - k)) q k
              _ = finiteQPochhammerIn
                    (q ^ ((n + 1) - (k + 1) + 1)) q (k + 1) := by
                congr 2
                omega
          · have hnk : n ≤ k := Nat.le_of_not_gt hlt
            have hkeq : k = n := Nat.le_antisymm hkn hnk
            subst k
            simp

/-- **Full denominator-free q-factorial identity.**  The finite
q-Pochhammer product in row `n` is the product of the two would-be quotient
denominators and the recursive Gaussian coefficient.

Unlike a quotient formula, this identity is meaningful and true at roots of
unity, over positive-characteristic rings, and in the presence of zero
divisors. -/
theorem finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial
    {R : Type*} [CommRing R] (q : R) {n k : ℕ} (hk : k ≤ n) :
    finiteQPochhammerIn q q n =
      finiteQPochhammerIn q q k * finiteQPochhammerIn q q (n - k) *
        gaussianBinomial q n k := by
  calc
    finiteQPochhammerIn q q n =
        finiteQPochhammerIn q q ((n - k) + k) := by
      rw [Nat.sub_add_cancel hk]
    _ = finiteQPochhammerIn q q (n - k) *
        finiteQPochhammerIn (q ^ (n - k + 1)) q k :=
      finiteQPochhammerIn_self_add q (n - k) k
    _ = finiteQPochhammerIn q q (n - k) *
        (finiteQPochhammerIn q q k * gaussianBinomial q n k) := by
      rw [finiteQPochhammerIn_self_mul_gaussianBinomial q hk]
    _ = finiteQPochhammerIn q q k * finiteQPochhammerIn q q (n - k) *
        gaussianBinomial q n k := by
      ring

private def gaussianBinomialSummand
    {R : Type*} [CommRing R] (q z : R) (n k : ℕ) : R :=
  (-1 : R) ^ k * q ^ k.choose 2 * gaussianBinomial q n k * z ^ k

@[simp] private theorem gaussianBinomialSummand_zero
    {R : Type*} [CommRing R] (q z : R) (n : ℕ) :
    gaussianBinomialSummand q z n 0 = 1 := by
  simp [gaussianBinomialSummand]

private theorem choose_succ_two_core (k : ℕ) :
    (k + 1).choose 2 = k.choose 2 + k := by
  simpa [Nat.add_comm] using Nat.choose_succ_succ k 1

private theorem gaussianBinomialSummand_succ_succ
    {R : Type*} [CommRing R] (q z : R)
    (n k : ℕ) (hk : k ≤ n) :
    gaussianBinomialSummand q z (n + 1) (k + 1) =
      gaussianBinomialSummand q z n (k + 1) -
        z * q ^ n * gaussianBinomialSummand q z n k := by
  rw [gaussianBinomialSummand, gaussianBinomialSummand,
    gaussianBinomialSummand, gaussianBinomial_succ_succ]
  rw [choose_succ_two_core, pow_add, pow_succ, pow_succ]
  have hsum : k + (n - k) = n := Nat.add_sub_of_le hk
  have hqpow : q ^ k * q ^ (n - k) = q ^ n := by
    rw [← pow_add, hsum]
  ring_nf
  linear_combination
    -(gaussianBinomial q n k * z * z ^ k * (-1 : R) ^ k *
      q ^ k.choose 2) * hqpow

private theorem gaussianBinomialSummand_above
    {R : Type*} [CommRing R] (q z : R) (n : ℕ) :
    gaussianBinomialSummand q z n (n + 1) = 0 := by
  rw [gaussianBinomialSummand,
    gaussianBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)]
  ring

/-- **Finite q-binomial theorem over a commutative ring.**  The
denominator-free Gaussian coefficients expand the finite q-Pochhammer
product for every `q` and `z`, including roots of unity and zero. -/
theorem finite_qBinomial_theorem
    {R : Type*} [CommRing R] (q z : R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : R) ^ k * q ^ k.choose 2 *
        gaussianBinomial q n k * z ^ k) =
      finiteQPochhammerIn z q n := by
  change (∑ k ∈ Finset.range (n + 1),
    gaussianBinomialSummand q z n k) = _
  induction n with
  | zero => simp [finiteQPochhammerIn]
  | succ n ih =>
      have hrec :
          (∑ k ∈ Finset.range (n + 1),
              gaussianBinomialSummand q z (n + 1) (k + 1)) =
            ∑ k ∈ Finset.range (n + 1),
              (gaussianBinomialSummand q z n (k + 1) -
                z * q ^ n * gaussianBinomialSummand q z n k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact gaussianBinomialSummand_succ_succ q z n k
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      have htail :
          1 + (∑ k ∈ Finset.range (n + 1),
              gaussianBinomialSummand q z n (k + 1)) =
            ∑ k ∈ Finset.range (n + 1),
              gaussianBinomialSummand q z n k := by
        calc
          1 + (∑ k ∈ Finset.range (n + 1),
              gaussianBinomialSummand q z n (k + 1)) =
              ∑ k ∈ Finset.range (n + 2),
                gaussianBinomialSummand q z n k := by
            have hs := (Finset.sum_range_succ'
              (fun k => gaussianBinomialSummand q z n k) (n + 1)).symm
            rw [show n + 1 + 1 = n + 2 by omega] at hs
            simpa [add_comm] using hs
          _ = (∑ k ∈ Finset.range (n + 1),
                gaussianBinomialSummand q z n k) +
              gaussianBinomialSummand q z n (n + 1) := by
            exact Finset.sum_range_succ _ _
          _ = _ := by
            rw [gaussianBinomialSummand_above, add_zero]
      rw [show n + 1 + 1 = n + 2 by omega, Finset.sum_range_succ']
      rw [gaussianBinomialSummand_zero, hrec, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
      calc
        (∑ x ∈ Finset.range (n + 1),
              gaussianBinomialSummand q z n (x + 1)) -
              z * q ^ n *
                (∑ i ∈ Finset.range (n + 1),
                  gaussianBinomialSummand q z n i) + 1 =
            (1 + ∑ x ∈ Finset.range (n + 1),
                gaussianBinomialSummand q z n (x + 1)) -
              z * q ^ n *
                (∑ i ∈ Finset.range (n + 1),
                  gaussianBinomialSummand q z n i) := by
          ring
        _ = (∑ i ∈ Finset.range (n + 1),
                gaussianBinomialSummand q z n i) -
              z * q ^ n *
                (∑ i ∈ Finset.range (n + 1),
                  gaussianBinomialSummand q z n i) := by
          rw [htail]
        _ = (1 - z * q ^ n) *
              (∑ i ∈ Finset.range (n + 1),
                gaussianBinomialSummand q z n i) := by
          ring
        _ = finiteQPochhammerIn z q (n + 1) := by
          rw [ih, finiteQPochhammerIn_succ]
          ring

end Fabius
