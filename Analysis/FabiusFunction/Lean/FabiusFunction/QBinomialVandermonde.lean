import FabiusFunction.FiniteQBinomialCore
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Interval

/-!
# The q-Vandermonde convolution

This module proves the two finite q-Vandermonde convolutions for the
division-free Gaussian coefficient `Fabius.gaussianBinomial`.  Both formulas
hold over an arbitrary commutative semiring, at every value of `q`, and for
all natural indices.  In particular, no quotient, cancellation, or
nonvanishing hypothesis is hidden at `q = 0`, at roots of unity, or in rings
with zero divisors.

The zero extension of the Gaussian triangle lets the classical finite sum
over all integral indices be written simply as a sum over `range (r + 1)`:

`[m+n choose r]_q = sum_j q^((m-j)(r-j)) [m choose j]_q [n choose r-j]_q`.

The second orientation follows by swapping the two blocks and reflecting the
finite sum.  Reflecting once more at `r = m`, and using Gaussian symmetry,
gives the central square-weighted identity

`[m+n choose m]_q = sum_j q^(j^2) [m choose j]_q [n choose j]_q`.

## Main results

* `gaussianBinomial_add_vandermonde` -- the first q-Vandermonde
  convolution, with weight `q ^ ((m - j) * (r - j))`.
* `gaussianBinomial_add_vandermonde'` -- the block-reversed orientation,
  with weight `q ^ (j * (n - (r - j)))`.
* `gaussianBinomial_add_central` -- the central specialization with the
  square weight `q ^ (j * j)`.
* `gaussianBinomial_add_central_min` -- the same identity with its exact
  nonzero support truncated at `min m n`.
* `gaussianBinomial_two_mul_add_shifted_central` and the two negative-shift
  forms give the monograph's shifted central convolution without introducing
  a signed-index Gaussian coefficient.
* The finite-range and literal finite-support integer-sum forms use the total
  integer-indexed Gaussian coefficient from `FiniteQBinomialCore` to package
  the same convolution for an arbitrary integer shift exactly as in the
  monograph.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

/-- The summand in the first q-Vandermonde convolution.  Natural
subtraction is harmless outside the admissible range because one of the two
zero-extended Gaussian coefficients then vanishes. -/
private def qVandermondeSummand {R : Type*} [CommSemiring R]
    (q : R) (m n r j : ℕ) : R :=
  q ^ ((m - j) * (r - j)) * gaussianBinomial q m j *
    gaussianBinomial q n (r - j)

/-- The summand recurrence that drives q-Vandermonde.  It is q-Pascal in
the second Gaussian factor, with the common power
`q ^ ((m + n) - r)` pulled out of its second term. -/
private theorem qVandermondeSummand_succ
    {R : Type*} [CommSemiring R]
    (q : R) (m n r j : ℕ) (hj : j ≤ r) :
    qVandermondeSummand q m (n + 1) (r + 1) j =
      qVandermondeSummand q m n (r + 1) j +
        q ^ ((m + n) - r) * qVandermondeSummand q m n r j := by
  by_cases hjm : j ≤ m
  · by_cases hjn : r - j ≤ n
    · have hindex : r + 1 - j = (r - j) + 1 := by omega
      have hsplit : (m + n) - r = (m - j) + (n - (r - j)) := by omega
      have hexponent :
          (m - j) * ((r - j) + 1) + (n - (r - j)) =
            ((m + n) - r) + (m - j) * (r - j) := by
        rw [Nat.mul_add, Nat.mul_one, hsplit]
        omega
      have hpow :
          q ^ ((m - j) * ((r - j) + 1)) * q ^ (n - (r - j)) =
            q ^ ((m + n) - r) * q ^ ((m - j) * (r - j)) := by
        rw [← pow_add, ← pow_add, hexponent]
      have hsecond :
          q ^ ((m - j) * ((r - j) + 1)) *
                gaussianBinomial q m j *
                (q ^ (n - (r - j)) *
                  gaussianBinomial q n (r - j)) =
            q ^ ((m + n) - r) *
              (q ^ ((m - j) * (r - j)) *
                gaussianBinomial q m j *
                  gaussianBinomial q n (r - j)) := by
        calc
          q ^ ((m - j) * ((r - j) + 1)) *
                gaussianBinomial q m j *
                (q ^ (n - (r - j)) *
                  gaussianBinomial q n (r - j)) =
              (q ^ ((m - j) * ((r - j) + 1)) *
                  q ^ (n - (r - j))) *
                (gaussianBinomial q m j *
                  gaussianBinomial q n (r - j)) := by
            ac_rfl
          _ = (q ^ ((m + n) - r) *
                  q ^ ((m - j) * (r - j))) *
                (gaussianBinomial q m j *
                  gaussianBinomial q n (r - j)) := by
            rw [hpow]
          _ = q ^ ((m + n) - r) *
              (q ^ ((m - j) * (r - j)) *
                gaussianBinomial q m j *
                  gaussianBinomial q n (r - j)) := by
            ac_rfl
      unfold qVandermondeSummand
      rw [hindex, gaussianBinomial_succ_succ, mul_add, hsecond]
    · have hlt : n < r - j := Nat.lt_of_not_ge hjn
      have hcurrent : gaussianBinomial q n (r - j) = 0 :=
        gaussianBinomial_eq_zero_of_lt q hlt
      have hnext : gaussianBinomial q n (r + 1 - j) = 0 :=
        gaussianBinomial_eq_zero_of_lt q (by omega)
      have hnextRow : gaussianBinomial q (n + 1) (r + 1 - j) = 0 :=
        gaussianBinomial_eq_zero_of_lt q (by omega)
      unfold qVandermondeSummand
      rw [hcurrent, hnext, hnextRow]
      simp
  · have hlt : m < j := Nat.lt_of_not_ge hjm
    have hzero : gaussianBinomial q m j = 0 :=
      gaussianBinomial_eq_zero_of_lt q hlt
    simp [qVandermondeSummand, hzero]

/-- **The first q-Vandermonde convolution.**  For every commutative
semiring and all natural indices,

`[m+n choose r]_q = ∑_{j=0}^r q^((m-j)(r-j))
  [m choose j]_q [n choose r-j]_q`.

The formula is valid without an admissibility assumption on `r`: when
`m + n < r`, zero extension makes both sides vanish.  The proof is a direct
induction from q-Pascal and therefore never cancels a power of `q`. -/
theorem gaussianBinomial_add_vandermonde
    {R : Type*} [CommSemiring R]
    (q : R) (m n r : ℕ) :
    gaussianBinomial q (m + n) r =
      ∑ j ∈ Finset.range (r + 1),
        q ^ ((m - j) * (r - j)) * gaussianBinomial q m j *
          gaussianBinomial q n (r - j) := by
  change gaussianBinomial q (m + n) r =
    ∑ j ∈ Finset.range (r + 1), qVandermondeSummand q m n r j
  induction n generalizing r with
  | zero =>
      simp only [Nat.add_zero]
      calc
        gaussianBinomial q m r = qVandermondeSummand q m 0 r r := by
          simp [qVandermondeSummand]
        _ = ∑ j ∈ Finset.range (r + 1),
              qVandermondeSummand q m 0 r j := by
          symm
          apply Finset.sum_eq_single r
          · intro j hj hne
            have hjlt : j < r := by
              have hjle : j ≤ r :=
                Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              omega
            have hzero : gaussianBinomial q 0 (r - j) = 0 :=
              gaussianBinomial_eq_zero_of_lt q (by omega)
            simp [qVandermondeSummand, hzero]
          · simp
  | succ n ih =>
      cases r with
      | zero =>
          simp [qVandermondeSummand]
      | succ r =>
          have hsum :
              (∑ j ∈ Finset.range (r + 2),
                  qVandermondeSummand q m (n + 1) (r + 1) j) =
                (∑ j ∈ Finset.range (r + 2),
                  qVandermondeSummand q m n (r + 1) j) +
                  q ^ ((m + n) - r) *
                    ∑ j ∈ Finset.range (r + 1),
                      qVandermondeSummand q m n r j := by
            have hlast :
                qVandermondeSummand q m (n + 1) (r + 1) (r + 1) =
                  qVandermondeSummand q m n (r + 1) (r + 1) := by
              simp [qVandermondeSummand]
            calc
              (∑ j ∈ Finset.range (r + 2),
                    qVandermondeSummand q m (n + 1) (r + 1) j) =
                  (∑ j ∈ Finset.range (r + 1),
                    qVandermondeSummand q m (n + 1) (r + 1) j) +
                    qVandermondeSummand q m (n + 1) (r + 1) (r + 1) := by
                rw [show r + 2 = (r + 1) + 1 by omega,
                  Finset.sum_range_succ]
              _ = (∑ j ∈ Finset.range (r + 1),
                    (qVandermondeSummand q m n (r + 1) j +
                      q ^ ((m + n) - r) *
                        qVandermondeSummand q m n r j)) +
                    qVandermondeSummand q m n (r + 1) (r + 1) := by
                rw [hlast]
                congr 1
                apply Finset.sum_congr rfl
                intro j hj
                exact qVandermondeSummand_succ q m n r j
                  (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
              _ = ((∑ j ∈ Finset.range (r + 1),
                      qVandermondeSummand q m n (r + 1) j) +
                    qVandermondeSummand q m n (r + 1) (r + 1)) +
                  q ^ ((m + n) - r) *
                    ∑ j ∈ Finset.range (r + 1),
                      qVandermondeSummand q m n r j := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum]
                ac_rfl
              _ = (∑ j ∈ Finset.range (r + 2),
                    qVandermondeSummand q m n (r + 1) j) +
                  q ^ ((m + n) - r) *
                    ∑ j ∈ Finset.range (r + 1),
                      qVandermondeSummand q m n r j := by
                congr 1
                exact (Finset.sum_range_succ
                  (fun j => qVandermondeSummand q m n (r + 1) j)
                  (r + 1)).symm
          calc
            gaussianBinomial q (m + (n + 1)) (r + 1) =
                gaussianBinomial q (m + n) (r + 1) +
                  q ^ ((m + n) - r) * gaussianBinomial q (m + n) r := by
              rw [show m + (n + 1) = (m + n) + 1 by omega,
                gaussianBinomial_succ_succ]
            _ = (∑ j ∈ Finset.range (r + 2),
                  qVandermondeSummand q m n (r + 1) j) +
                q ^ ((m + n) - r) *
                  ∑ j ∈ Finset.range (r + 1),
                    qVandermondeSummand q m n r j := by
              rw [ih (r + 1), ih r]
            _ = ∑ j ∈ Finset.range (r + 2),
                  qVandermondeSummand q m (n + 1) (r + 1) j := hsum.symm

/-- **The block-reversed q-Vandermonde convolution.**  Swapping the two
blocks in `gaussianBinomial_add_vandermonde` and reflecting the summation
index gives

`[m+n choose r]_q = ∑_{j=0}^r q^(j (n-(r-j)))
  [m choose j]_q [n choose r-j]_q`.

On every nonzero summand, the natural exponent `n - (r - j)` is the usual
integer expression `n - r + j`; its nested-subtraction form remains valid
without side conditions. -/
theorem gaussianBinomial_add_vandermonde'
    {R : Type*} [CommSemiring R]
    (q : R) (m n r : ℕ) :
    gaussianBinomial q (m + n) r =
      ∑ j ∈ Finset.range (r + 1),
        q ^ (j * (n - (r - j))) * gaussianBinomial q m j *
          gaussianBinomial q n (r - j) := by
  let f : ℕ → R := fun j =>
    q ^ ((n - j) * (r - j)) * gaussianBinomial q n j *
      gaussianBinomial q m (r - j)
  have hreflect := Finset.sum_range_reflect f (r + 1)
  calc
    gaussianBinomial q (m + n) r =
        gaussianBinomial q (n + m) r := by rw [Nat.add_comm]
    _ = ∑ j ∈ Finset.range (r + 1), f j := by
      simpa only [f] using gaussianBinomial_add_vandermonde q n m r
    _ = ∑ j ∈ Finset.range (r + 1), f (r - j) := by
      symm
      simpa only [Nat.add_sub_cancel] using hreflect
    _ = ∑ j ∈ Finset.range (r + 1),
          q ^ (j * (n - (r - j))) * gaussianBinomial q m j *
            gaussianBinomial q n (r - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjr : j ≤ r :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      simp only [f, Nat.sub_sub_self hjr]
      rw [Nat.mul_comm (n - (r - j)) j]
      ac_rfl

/-- **Central q-Vandermonde.**  The central Gaussian coefficient is the
square-weighted scalar product of rows `m` and `n`:

`[m+n choose m]_q = ∑_{j=0}^m q^(j^2)
  [m choose j]_q [n choose j]_q`.

This remains true when `j > n`, because the second Gaussian coefficient is
then zero. -/
theorem gaussianBinomial_add_central
    {R : Type*} [CommSemiring R]
    (q : R) (m n : ℕ) :
    gaussianBinomial q (m + n) m =
      ∑ j ∈ Finset.range (m + 1),
        q ^ (j * j) * gaussianBinomial q m j *
          gaussianBinomial q n j := by
  let f : ℕ → R := fun j =>
    q ^ ((m - j) * (m - j)) * gaussianBinomial q m j *
      gaussianBinomial q n (m - j)
  have hreflect := Finset.sum_range_reflect f (m + 1)
  calc
    gaussianBinomial q (m + n) m =
        ∑ j ∈ Finset.range (m + 1), f j := by
      simpa only [f] using gaussianBinomial_add_vandermonde q m n m
    _ = ∑ j ∈ Finset.range (m + 1), f (m - j) := by
      symm
      simpa only [Nat.add_sub_cancel] using hreflect
    _ = ∑ j ∈ Finset.range (m + 1),
          q ^ (j * j) * gaussianBinomial q m j *
            gaussianBinomial q n j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j ≤ m :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      simp only [f, Nat.sub_sub_self hjm]
      rw [gaussianBinomial_symm q hjm]

/-- **Central q-Vandermonde on its exact support.**  Terms above
`min m n` vanish, so the central convolution may be truncated to the
intersection of the two Gaussian rows:

`[m+n choose m]_q = ∑_{j=0}^{min(m,n)} q^(j^2)
  [m choose j]_q [n choose j]_q`. -/
theorem gaussianBinomial_add_central_min
    {R : Type*} [CommSemiring R]
    (q : R) (m n : ℕ) :
    gaussianBinomial q (m + n) m =
      ∑ j ∈ Finset.range (min m n + 1),
        q ^ (j * j) * gaussianBinomial q m j *
          gaussianBinomial q n j := by
  rw [gaussianBinomial_add_central]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro j hj hnot
  have hjm : j ≤ m :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  by_cases hmn : m ≤ n
  · have : j ∈ Finset.range (min m n + 1) := by
      rw [Nat.min_eq_left hmn]
      exact hj
    exact (hnot this).elim
  · have hnm : n ≤ m := Nat.le_of_not_ge hmn
    have hnj : n < j := by
      have hminj : min m n < j := by
        have hjnot : ¬ j ≤ min m n := by
          simpa only [Finset.mem_range, Nat.lt_succ_iff] using hnot
        exact Nat.lt_of_not_ge hjnot
      rwa [Nat.min_eq_right hnm] at hminj
    rw [gaussianBinomial_eq_zero_of_lt q hnj, mul_zero]

/-! ## Shifted central forms -/

/-- **Positive shifted-central q-Vandermonde.**  This is total in `k`:

`[2N choose N+k]_q = ∑_{ℓ=0}^N q^(ℓ(ℓ+k))
  [N choose ℓ]_q [N choose ℓ+k]_q`.

When `N < k`, zero extension makes both sides vanish. -/
theorem gaussianBinomial_two_mul_add_shifted_central
    {R : Type*} [CommSemiring R]
    (q : R) (N k : ℕ) :
    gaussianBinomial q (2 * N) (N + k) =
      ∑ ℓ ∈ Finset.range (N + 1),
        q ^ (ℓ * (ℓ + k)) * gaussianBinomial q N ℓ *
          gaussianBinomial q N (ℓ + k) := by
  let f : ℕ → R := fun j =>
    q ^ ((N - j) * (N + k - j)) * gaussianBinomial q N j *
      gaussianBinomial q N (N + k - j)
  have hreflect := Finset.sum_range_reflect f (N + 1)
  calc
    gaussianBinomial q (2 * N) (N + k) =
        ∑ j ∈ Finset.range (N + k + 1), f j := by
      simpa only [two_mul, f] using
        gaussianBinomial_add_vandermonde q N N (N + k)
    _ = ∑ j ∈ Finset.range (N + 1), f j := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _hj hnot
      have hNj : N < j := by
        simp only [Finset.mem_range, Nat.not_lt] at hnot
        omega
      simp [f, gaussianBinomial_eq_zero_of_lt q hNj]
    _ = ∑ ℓ ∈ Finset.range (N + 1), f (N - ℓ) := by
      symm
      simpa only [Nat.add_sub_cancel] using hreflect
    _ = ∑ ℓ ∈ Finset.range (N + 1),
          q ^ (ℓ * (ℓ + k)) * gaussianBinomial q N ℓ *
            gaussianBinomial q N (ℓ + k) := by
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      have hℓN : ℓ ≤ N :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
      have hshift : N + k - (N - ℓ) = ℓ + k := by omega
      simp only [f, Nat.sub_sub_self hℓN, hshift]
      rw [gaussianBinomial_symm q hℓN]

/-- **Negative shifted-central q-Vandermonde, reflected support.**  Under
`k ≤ N`, row symmetry identifies `[2N choose N-k]_q` with the positive
shift.  The right side is therefore literally the positive-shift sum. -/
theorem gaussianBinomial_two_mul_sub_shifted_central
    {R : Type*} [CommSemiring R]
    (q : R) (N k : ℕ) (hk : k ≤ N) :
    gaussianBinomial q (2 * N) (N - k) =
      ∑ ℓ ∈ Finset.range (N + 1),
        q ^ (ℓ * (ℓ + k)) * gaussianBinomial q N ℓ *
          gaussianBinomial q N (ℓ + k) := by
  calc
    gaussianBinomial q (2 * N) (N - k) =
        gaussianBinomial q (2 * N) (N + k) := by
      have hsymm :
          gaussianBinomial q (2 * N) (2 * N - (N + k)) =
            gaussianBinomial q (2 * N) (N + k) :=
        gaussianBinomial_symm q (by omega)
      have hindex : 2 * N - (N + k) = N - k := by omega
      simpa only [hindex] using hsymm
    _ = _ := gaussianBinomial_two_mul_add_shifted_central q N k

/-- **Negative shifted-central q-Vandermonde, literal support.**  This is
the monograph's `K = -k` formula with the exact natural support
`k ≤ ℓ ≤ N`:

`[2N choose N-k]_q = ∑_{ℓ=k}^N q^(ℓ(ℓ-k))
  [N choose ℓ]_q [N choose ℓ-k]_q`. -/
theorem gaussianBinomial_two_mul_sub_shifted_central_Icc
    {R : Type*} [CommSemiring R]
    (q : R) (N k : ℕ) (hk : k ≤ N) :
    gaussianBinomial q (2 * N) (N - k) =
      ∑ ℓ ∈ Finset.Icc k N,
        q ^ (ℓ * (ℓ - k)) * gaussianBinomial q N ℓ *
          gaussianBinomial q N (ℓ - k) := by
  calc
    gaussianBinomial q (2 * N) (N - k) =
        ∑ j ∈ Finset.range (N - k + 1),
          q ^ ((N - j) * (N - k - j)) * gaussianBinomial q N j *
            gaussianBinomial q N (N - k - j) := by
      simpa only [two_mul] using
        gaussianBinomial_add_vandermonde q N N (N - k)
    _ = ∑ ℓ ∈ Finset.Icc k N,
          q ^ (ℓ * (ℓ - k)) * gaussianBinomial q N ℓ *
            gaussianBinomial q N (ℓ - k) := by
      apply Finset.sum_bij (fun j _ => N - j)
      · intro j hj
        have hj' := Finset.mem_range.mp hj
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro a ha b hb hab
        have ha' := Finset.mem_range.mp ha
        have hb' := Finset.mem_range.mp hb
        omega
      · intro ℓ hℓ
        have hℓ' := Finset.mem_Icc.mp hℓ
        refine ⟨N - ℓ, ?_, ?_⟩
        · exact Finset.mem_range.mpr (by omega)
        · omega
      · intro j hj
        have hj' := Finset.mem_range.mp hj
        have hjN : j ≤ N := by omega
        have hsub : N - k - j = N - j - k := by omega
        rw [hsub, gaussianBinomial_symm q hjN]

/-- **Shifted-central q-Vandermonde for an arbitrary integer shift.**

The lower index is interpreted through `gaussianBinomialInt`, hence is zero
outside `0, …, N`.  The report's sum over every integer may therefore be
trimmed exactly to `ℓ = 0, …, N`:

`[2N choose N+k]_q = ∑_{ℓ=0}^N q^(ℓ(ℓ+k))
  [N choose ℓ]_q [N choose ℓ+k]_q`.

The exponent is written with `Int.toNat`.  Whenever the second Gaussian
factor is nonzero, `ℓ+k ≥ 0`, so this is literally the displayed exponent;
when it is negative, the whole summand is zero.  Thus the theorem is total in
`k : ℤ`, including `|k| > N`, over every commutative semiring and without
division or cancellation. -/
theorem gaussianBinomial_two_mul_int_shifted_central
    {R : Type*} [CommSemiring R]
    (q : R) (N : ℕ) (k : ℤ) :
    gaussianBinomialInt q (2 * N) ((N : ℤ) + k) =
      ∑ ℓ ∈ Finset.range (N + 1),
        q ^ (ℓ * (((ℓ : ℤ) + k).toNat)) * gaussianBinomial q N ℓ *
          gaussianBinomialInt q N ((ℓ : ℤ) + k) := by
  cases k with
  | ofNat k =>
      change gaussianBinomialInt q (2 * N) ((N : ℤ) + (k : ℤ)) =
        ∑ ℓ ∈ Finset.range (N + 1),
          q ^ (ℓ * (((ℓ : ℤ) + (k : ℤ)).toNat)) *
            gaussianBinomial q N ℓ *
              gaussianBinomialInt q N ((ℓ : ℤ) + (k : ℤ))
      have hleft : (N : ℤ) + k = ((N + k : ℕ) : ℤ) := by
        omega
      rw [hleft, gaussianBinomialInt_ofNat]
      calc
        gaussianBinomial q (2 * N) (N + k) =
            ∑ ℓ ∈ Finset.range (N + 1),
              q ^ (ℓ * (ℓ + k)) * gaussianBinomial q N ℓ *
                gaussianBinomial q N (ℓ + k) :=
          gaussianBinomial_two_mul_add_shifted_central q N k
        _ = ∑ ℓ ∈ Finset.range (N + 1),
              q ^ (ℓ * (((ℓ : ℤ) + k).toNat)) * gaussianBinomial q N ℓ *
                gaussianBinomialInt q N ((ℓ : ℤ) + k) := by
          apply Finset.sum_congr rfl
          intro ℓ _hℓ
          have htoNat : (((ℓ : ℤ) + (k : ℤ)).toNat) = ℓ + k := by
            omega
          have hshift : (ℓ : ℤ) + (k : ℤ) = ((ℓ + k : ℕ) : ℤ) := by
            omega
          rw [htoNat, hshift, gaussianBinomialInt_ofNat]
  | negSucc k =>
      let d := k + 1
      have hk : Int.negSucc k = -(d : ℤ) := by
        omega
      rw [hk]
      change gaussianBinomialInt q (2 * N) ((N : ℤ) - d) =
        ∑ ℓ ∈ Finset.range (N + 1),
          q ^ (ℓ * (((ℓ : ℤ) - d).toNat)) * gaussianBinomial q N ℓ *
            gaussianBinomialInt q N ((ℓ : ℤ) - d)
      by_cases hd : d ≤ N
      · have hleft : (N : ℤ) - d = ((N - d : ℕ) : ℤ) := by
          omega
        rw [hleft, gaussianBinomialInt_ofNat]
        calc
          gaussianBinomial q (2 * N) (N - d) =
              ∑ ℓ ∈ Finset.Icc d N,
                q ^ (ℓ * (ℓ - d)) * gaussianBinomial q N ℓ *
                  gaussianBinomial q N (ℓ - d) :=
            gaussianBinomial_two_mul_sub_shifted_central_Icc q N d hd
          _ = ∑ ℓ ∈ Finset.range (N + 1),
                q ^ (ℓ * (((ℓ : ℤ) - d).toNat)) *
                  gaussianBinomial q N ℓ *
                    gaussianBinomialInt q N ((ℓ : ℤ) - d) := by
            calc
              (∑ ℓ ∈ Finset.Icc d N,
                  q ^ (ℓ * (ℓ - d)) * gaussianBinomial q N ℓ *
                    gaussianBinomial q N (ℓ - d)) =
                  ∑ ℓ ∈ Finset.Icc d N,
                    q ^ (ℓ * (((ℓ : ℤ) - d).toNat)) *
                      gaussianBinomial q N ℓ *
                        gaussianBinomialInt q N ((ℓ : ℤ) - d) := by
                apply Finset.sum_congr rfl
                intro ℓ hℓ
                have hℓ' := Finset.mem_Icc.mp hℓ
                have hshift :
                    (ℓ : ℤ) - d = ((ℓ - d : ℕ) : ℤ) := by
                  omega
                rw [hshift, gaussianBinomialInt_ofNat]
                simp
              _ = ∑ ℓ ∈ Finset.range (N + 1),
                    q ^ (ℓ * (((ℓ : ℤ) - d).toNat)) *
                      gaussianBinomial q N ℓ *
                        gaussianBinomialInt q N ((ℓ : ℤ) - d) := by
                apply Finset.sum_subset
                · intro ℓ hℓ
                  have hℓ' := Finset.mem_Icc.mp hℓ
                  exact Finset.mem_range.mpr (by omega)
                · intro ℓ hℓ hnot
                  have hℓN : ℓ ≤ N :=
                    Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
                  have hℓd : ℓ < d := by
                    by_contra h
                    exact hnot
                      (Finset.mem_Icc.mpr ⟨Nat.le_of_not_gt h, hℓN⟩)
                  have hneg : (ℓ : ℤ) - d < 0 := by omega
                  rw [gaussianBinomialInt_eq_zero_of_neg q N hneg, mul_zero]
      · have hdN : N < d := Nat.lt_of_not_ge hd
        have hleft : (N : ℤ) - d < 0 := by omega
        rw [gaussianBinomialInt_eq_zero_of_neg q (2 * N) hleft]
        symm
        apply Finset.sum_eq_zero
        intro ℓ hℓ
        have hℓN : ℓ ≤ N :=
          Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
        have hneg : (ℓ : ℤ) - d < 0 := by omega
        rw [gaussianBinomialInt_eq_zero_of_neg q N hneg, mul_zero]

/-- **Literal integer-sum shifted-central q-Vandermonde.**  With both lower
indices extended by zero, the monograph's sum may be written over every
integer without choosing separate positive- and negative-shift ranges:

`[2N choose N+k]_q = ∑_{ℓ∈ℤ} q^(ℓ(ℓ+k))
  [N choose ℓ]_q [N choose ℓ+k]_q`.

The `finsum` is genuinely finite: its support lies in `0 ≤ ℓ ≤ N`.  The
natural exponent displayed in Lean agrees with the integer product on every
possibly nonzero summand. -/
theorem gaussianBinomial_two_mul_int_shifted_central_finsum
    {R : Type*} [CommSemiring R] (q : R) (N : ℕ) (k : ℤ) :
    gaussianBinomialInt q (2 * N) ((N : ℤ) + k) =
      ∑ᶠ ℓ : ℤ,
        q ^ (ℓ.toNat * (ℓ + k).toNat) * gaussianBinomialInt q N ℓ *
          gaussianBinomialInt q N (ℓ + k) := by
  let f : ℤ → R := fun ℓ =>
    q ^ (ℓ.toNat * (ℓ + k).toNat) * gaussianBinomialInt q N ℓ *
      gaussianBinomialInt q N (ℓ + k)
  have hsupp : Function.support f ⊆
      (Finset.Icc (0 : ℤ) (N : ℤ) : Set ℤ) := by
    intro ℓ hℓ
    rw [Function.mem_support] at hℓ
    have h0 : 0 ≤ ℓ := by
      by_contra h
      apply hℓ
      simp [f, gaussianBinomialInt_eq_zero_of_neg q N (lt_of_not_ge h)]
    have hN : ℓ ≤ (N : ℤ) := by
      by_contra h
      apply hℓ
      simp [f, gaussianBinomialInt_eq_zero_of_lt q N (lt_of_not_ge h)]
    exact Finset.mem_Icc.mpr ⟨h0, hN⟩
  calc
    gaussianBinomialInt q (2 * N) ((N : ℤ) + k) =
        ∑ ℓ ∈ Finset.range (N + 1),
          q ^ (ℓ * (((ℓ : ℤ) + k).toNat)) * gaussianBinomial q N ℓ *
            gaussianBinomialInt q N ((ℓ : ℤ) + k) :=
      gaussianBinomial_two_mul_int_shifted_central q N k
    _ = ∑ ℓ ∈ Finset.Icc (0 : ℤ) (N : ℤ), f ℓ := by
      rw [Int.Icc_eq_finset_map, Finset.sum_map]
      simp [f]
    _ = ∑ᶠ ℓ : ℤ, f ℓ :=
      (finsum_eq_sum_of_support_subset f hsupp).symm
    _ = _ := rfl

end Fabius
