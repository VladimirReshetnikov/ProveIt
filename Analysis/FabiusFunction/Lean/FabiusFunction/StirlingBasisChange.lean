import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Eval.SMul
import FabiusFunction.BinomialInversion

/-!
# Stirling numbers: factorial bases, orthogonality, and the surjection formula

Mathlib defines the Stirling numbers of both kinds by their triangular
recurrences (`Nat.stirlingFirst`, `Nat.stirlingSecond`).  This module proves
the identities that make them *change-of-basis* matrices between the monomial
basis `X^k` and the factorial bases: the rising factorials
`ascPochhammer S n = X (X+1) ⋯ (X+n-1)` and the falling factorials
`descPochhammer R n = X (X-1) ⋯ (X-n+1)`.

* `ascPochhammer S n = ∑_k c(n,k) X^k` and
  `descPochhammer R n = ∑_k s(n,k) X^k`, where `c` is the unsigned and
  `s(n,k) = (-1)^(n-k) c(n,k)` the signed first-kind number;
* `X^n = ∑_k S(n,k) descPochhammer R k` and
  `X^n = ∑_k (-1)^(n-k) S(n,k) ascPochhammer R k`;
* the two matrices `S` and `s` are mutually inverse, in both orders;
* evaluating the falling-factorial expansion at a natural number `m` gives
  `m^n = ∑_k S(n,k) m^{\underline k} = ∑_k S(n,k) k! C(m,k)`, and binomial
  inversion of this identity is the surjection formula
  `k! S(n,k) = ∑_j (-1)^(k-j) C(k,j) j^n`;
* the two-sum recurrence `c(n+1,k+1) = ∑_j c(n,j) C(j,k)`
  (`stirlingFirst_succ_succ_eq_sum_choose`), the single home of an identity that two
  mutually independent downstream modules both need;
* the Stirling transform `g n = ∑_k S(n,k) f k` is inverted by
  `f n = ∑_k s(n,k) g k`, for sequences in any additive commutative group.

All polynomial identities hold over an arbitrary commutative (semi)ring: the
first-kind expansions are proved by comparing coefficients along the
one-step recurrences, and the second-kind expansion by the single relation
`X · (X)_k = (X)_{k+1} + k (X)_k`.  No division, characteristic, or
domain hypothesis is used anywhere; the surjection formula is an identity
in `ℤ`, with the divided form recorded over `ℚ`.

The module also records a general fact used to read coefficients off a
triangular polynomial family: if `P k` has leading coefficient one in
degree `k`, a vanishing combination `∑_{k ≤ N} a k • P k = 0` forces every
`a k = 0` (`eq_zero_of_sum_smul_eq_zero`), so coefficients in such a basis
are unique (`eq_of_sum_smul_eq_sum_smul`).

## Main results

* `ascPochhammer_eq_sum_monomial_stirlingFirst`,
  `descPochhammer_eq_sum_monomial_signedStirlingFirst`,
  `X_pow_eq_sum_stirlingSecond_mul_descPochhammer`,
  `X_pow_eq_sum_stirlingSecond_mul_ascPochhammer`: the four basis changes.
* `sum_range_stirlingSecond_mul_signedStirlingFirst` and
  `sum_range_signedStirlingFirst_mul_stirlingSecond`: the inverse-matrix
  relations (also in `Icc` form).
* `pow_eq_sum_stirlingSecond_mul_descFactorial`,
  `pow_eq_sum_stirlingSecond_mul_factorial_mul_choose`: the evaluated forms.
* `factorial_mul_stirlingSecond_eq_sum` and
  `stirlingSecond_eq_sum_div_factorial`: the surjection formula.
* `stirling_inversion`, `stirling_inversion_symm`,
  `stirling_inversion_iff`: the Stirling transform and its inverse.
* `sum_stirlingFirst_eq_factorial`: the row sum `∑_k c(n,k) = n!`.
* `sum_range_pow_eq_sum_stirlingSecond`: power sums through the factorial
  basis, `∑_{i ≤ N} i^m = ∑_k S(m,k) k! C(N+1,k+1)`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-! ### Signed Stirling numbers of the first kind -/

/-- The signed Stirling numbers of the first kind, `s(n,k) = (-1)^(n-k) c(n,k)`,
the coefficients of the falling factorial `X (X-1) ⋯ (X-n+1)`. -/
def signedStirlingFirst (n k : ℕ) : ℤ := (-1) ^ (n - k) * Nat.stirlingFirst n k

@[simp] theorem signedStirlingFirst_zero_zero : signedStirlingFirst 0 0 = 1 := by
  simp [signedStirlingFirst]

@[simp] theorem signedStirlingFirst_succ_zero (n : ℕ) : signedStirlingFirst (n + 1) 0 = 0 := by
  simp [signedStirlingFirst]

/-- Signed first-kind numbers vanish above the diagonal. -/
theorem signedStirlingFirst_eq_zero_of_lt {n k : ℕ} (h : n < k) :
    signedStirlingFirst n k = 0 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_eq_zero_of_lt h]

@[simp] theorem signedStirlingFirst_self (n : ℕ) : signedStirlingFirst n n = 1 := by
  simp [signedStirlingFirst, Nat.stirlingFirst_self]

/-- The signed first-kind recurrence `s(n+1,k+1) = s(n,k) - n s(n,k+1)`,
valid for all `n, k` (the boundary cases are covered by the vanishing above
the diagonal). -/
theorem signedStirlingFirst_succ_succ (n k : ℕ) :
    signedStirlingFirst (n + 1) (k + 1) =
      signedStirlingFirst n k - n * signedStirlingFirst n (k + 1) := by
  unfold signedStirlingFirst
  rw [Nat.stirlingFirst_succ_succ]
  rcases lt_or_ge n (k + 1) with h | h
  · rw [Nat.stirlingFirst_eq_zero_of_lt h]
    have hsub : n + 1 - (k + 1) = n - k := by omega
    rw [hsub]
    push_cast
    ring
  · have h1 : n + 1 - (k + 1) = n - (k + 1) + 1 := by omega
    have h2 : n - k = n - (k + 1) + 1 := by omega
    rw [h1, h2]
    push_cast
    ring

/-! ### Coefficients of monomial expansions and triangular families -/

/-- The `m`-th coefficient of `∑_{k ≤ n} c k X^k` is `c m` for `m ≤ n` and `0`
otherwise. -/
theorem coeff_sum_monomial_range {S : Type*} [Semiring S] (c : ℕ → S) (n m : ℕ) :
    coeff (∑ k ∈ Finset.range (n + 1), monomial k (c k)) m = if m ≤ n then c m else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_range]

/-- **Linear independence of a triangular polynomial family.**  If each `P k`
has `X^k`-coefficient one and no coefficients above degree `k`, then a
vanishing combination `∑_{k ≤ N} a k • P k = 0` has `a k = 0` for all
`k ≤ N`. -/
theorem eq_zero_of_sum_smul_eq_zero {R : Type*} [CommRing R] (P : ℕ → R[X])
    (hdiag : ∀ k, coeff (P k) k = 1) (hupper : ∀ k m, k < m → coeff (P k) m = 0) :
    ∀ (N : ℕ) (a : ℕ → R), (∑ k ∈ Finset.range (N + 1), a k • P k) = 0 →
      ∀ k ≤ N, a k = 0 := by
  intro N
  induction N with
  | zero =>
    intro a h k hk
    have hk0 : k = 0 := by omega
    subst hk0
    have := congrArg (fun p => coeff p 0) h
    simpa [coeff_smul, hdiag 0] using this
  | succ N ih =>
    intro a h k hk
    have htop : a (N + 1) = 0 := by
      have := congrArg (fun p => coeff p (N + 1)) h
      simp only [finsetSum_coeff, coeff_smul, smul_eq_mul, coeff_zero] at this
      rw [Finset.sum_range_succ, hdiag, mul_one, Finset.sum_eq_zero, zero_add] at this
      · exact this
      · intro j hj
        rw [hupper j (N + 1) (Finset.mem_range.mp hj), mul_zero]
    rcases Nat.lt_or_ge k (N + 1) with hlt | hge
    · apply ih a _ k (Nat.lt_succ_iff.mp hlt)
      rw [Finset.sum_range_succ, htop, zero_smul, add_zero] at h
      exact h
    · have hk' : k = N + 1 := by omega
      subst hk'
      exact htop

/-- **Uniqueness of coefficients in a triangular basis.**  Two expansions of
the same polynomial along a triangular family agree coefficientwise. -/
theorem eq_of_sum_smul_eq_sum_smul {R : Type*} [CommRing R] (P : ℕ → R[X])
    (hdiag : ∀ k, coeff (P k) k = 1) (hupper : ∀ k m, k < m → coeff (P k) m = 0)
    (N : ℕ) (a b : ℕ → R)
    (h : (∑ k ∈ Finset.range (N + 1), a k • P k) = ∑ k ∈ Finset.range (N + 1), b k • P k) :
    ∀ k ≤ N, a k = b k := by
  intro k hk
  have hsub := eq_zero_of_sum_smul_eq_zero P hdiag hupper N (fun k => a k - b k)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]) k hk
  exact sub_eq_zero.mp hsub

/-- Uniqueness of coefficients in a triangular basis, with the scalars written
as constant polynomials `C (a k) * P k`. -/
theorem eq_of_sum_C_mul_eq_sum_C_mul {R : Type*} [CommRing R] (P : ℕ → R[X])
    (hdiag : ∀ k, coeff (P k) k = 1) (hupper : ∀ k m, k < m → coeff (P k) m = 0)
    (N : ℕ) (a b : ℕ → R)
    (h : (∑ k ∈ Finset.range (N + 1), C (a k) * P k) =
      ∑ k ∈ Finset.range (N + 1), C (b k) * P k) :
    ∀ k ≤ N, a k = b k :=
  eq_of_sum_smul_eq_sum_smul P hdiag hupper N a b (by simpa only [smul_eq_C_mul] using h)

/-- Rearranging a triangular double expansion in a commutative ring: if the
inner coefficients vanish above the diagonal, then
`∑_j a j * ∑_{k ≤ j} b j k * P k = ∑_k (∑_j a j * b j k) * P k`. -/
theorem sum_mul_sum_mul_eq {A : Type*} [CommRing A] (a : ℕ → A) (b : ℕ → ℕ → A) (P : ℕ → A)
    (n : ℕ) (hb : ∀ j k, j < k → b j k = 0) :
    ∑ j ∈ Finset.range (n + 1), a j * ∑ k ∈ Finset.range (j + 1), b j k * P k =
      ∑ k ∈ Finset.range (n + 1), (∑ j ∈ Finset.range (n + 1), a j * b j k) * P k := by
  have hinner : ∀ j ∈ Finset.range (n + 1),
      ∑ k ∈ Finset.range (j + 1), b j k * P k = ∑ k ∈ Finset.range (n + 1), b j k * P k := by
    intro j hj
    have hjn : j < n + 1 := Finset.mem_range.mp hj
    apply Finset.sum_subset (Finset.range_mono (show j + 1 ≤ n + 1 by omega))
    intro k _ hk
    have hjk : j < k := by
      rw [Finset.mem_range, not_lt] at hk
      omega
    rw [hb j k hjk, zero_mul]
  rw [Finset.sum_congr rfl (fun j hj => by rw [hinner j hj])]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]

/-! ### First-kind numbers as coefficients of factorial polynomials -/

/-- **Rising factorials in the monomial basis:**
`X (X+1) ⋯ (X+n-1) = ∑_{k ≤ n} c(n,k) X^k`, over any commutative semiring. -/
theorem ascPochhammer_eq_sum_monomial_stirlingFirst (S : Type*) [CommSemiring S] (n : ℕ) :
    ascPochhammer S n = ∑ k ∈ Finset.range (n + 1), monomial k (Nat.stirlingFirst n k : S) := by
  induction n with
  | zero => simp [ascPochhammer_zero]
  | succ n ih =>
    rw [ascPochhammer_succ_right, ih]
    ext m
    rw [coeff_sum_monomial_range, mul_add, coeff_add, ← C_eq_natCast, coeff_mul_C,
      coeff_sum_monomial_range]
    cases m with
    | zero =>
      rw [coeff_mul_X_zero, if_pos (Nat.zero_le _), if_pos (Nat.zero_le _),
        Nat.stirlingFirst_succ_zero]
      cases n with
      | zero => simp
      | succ n => simp [Nat.stirlingFirst_succ_zero]
    | succ m =>
      rw [coeff_mul_X, coeff_sum_monomial_range]
      by_cases hm : m ≤ n
      · rw [if_pos (show m + 1 ≤ n + 1 by omega), if_pos hm, Nat.stirlingFirst_succ_succ]
        by_cases hm' : m + 1 ≤ n
        · rw [if_pos hm']
          push_cast
          ring
        · rw [if_neg hm', Nat.stirlingFirst_eq_zero_of_lt (show n < m + 1 by omega)]
          simp
      · rw [if_neg (show ¬ m + 1 ≤ n + 1 by omega), if_neg hm,
          if_neg (show ¬ m + 1 ≤ n by omega)]
        simp

/-- **Falling factorials in the monomial basis:**
`X (X-1) ⋯ (X-n+1) = ∑_{k ≤ n} s(n,k) X^k`, over any commutative ring. -/
theorem descPochhammer_eq_sum_monomial_signedStirlingFirst (R : Type*) [CommRing R] (n : ℕ) :
    descPochhammer R n =
      ∑ k ∈ Finset.range (n + 1), monomial k (signedStirlingFirst n k : R) := by
  induction n with
  | zero => simp [descPochhammer_zero]
  | succ n ih =>
    rw [descPochhammer_succ_right, ih]
    ext m
    rw [coeff_sum_monomial_range, mul_sub, coeff_sub, ← C_eq_natCast, coeff_mul_C,
      coeff_sum_monomial_range]
    cases m with
    | zero =>
      rw [coeff_mul_X_zero, if_pos (Nat.zero_le _), if_pos (Nat.zero_le _),
        signedStirlingFirst_succ_zero]
      cases n with
      | zero => simp
      | succ n => simp [signedStirlingFirst_succ_zero]
    | succ m =>
      rw [coeff_mul_X, coeff_sum_monomial_range]
      by_cases hm : m ≤ n
      · rw [if_pos (show m + 1 ≤ n + 1 by omega), if_pos hm, signedStirlingFirst_succ_succ]
        by_cases hm' : m + 1 ≤ n
        · rw [if_pos hm']
          push_cast
          ring
        · rw [if_neg hm', signedStirlingFirst_eq_zero_of_lt (show n < m + 1 by omega)]
          simp
      · rw [if_neg (show ¬ m + 1 ≤ n + 1 by omega), if_neg hm,
          if_neg (show ¬ m + 1 ≤ n by omega)]
        simp

/-- Coefficients of the falling factorial: `coeff (descPochhammer R n) m = s(n,m)`
for `m ≤ n`, and `0` above the degree. -/
theorem coeff_descPochhammer {R : Type*} [CommRing R] (n m : ℕ) :
    coeff (descPochhammer R n) m = if m ≤ n then (signedStirlingFirst n m : R) else 0 := by
  rw [descPochhammer_eq_sum_monomial_signedStirlingFirst, coeff_sum_monomial_range]

/-- Coefficients of the rising factorial: `coeff (ascPochhammer S n) m = c(n,m)`
for `m ≤ n`, and `0` above the degree. -/
theorem coeff_ascPochhammer {S : Type*} [CommSemiring S] (n m : ℕ) :
    coeff (ascPochhammer S n) m = if m ≤ n then (Nat.stirlingFirst n m : S) else 0 := by
  rw [ascPochhammer_eq_sum_monomial_stirlingFirst, coeff_sum_monomial_range]

/-- The falling factorials form a triangular family: diagonal coefficient one. -/
theorem coeff_descPochhammer_self {R : Type*} [CommRing R] (n : ℕ) :
    coeff (descPochhammer R n) n = 1 := by
  rw [coeff_descPochhammer, if_pos le_rfl, signedStirlingFirst_self, Int.cast_one]

/-- The falling factorials form a triangular family: no coefficients above the
degree. -/
theorem coeff_descPochhammer_of_lt {R : Type*} [CommRing R] {n m : ℕ} (h : n < m) :
    coeff (descPochhammer R n) m = 0 := by
  rw [coeff_descPochhammer, if_neg (by omega)]

/-- The rising factorials form a triangular family: diagonal coefficient one. -/
theorem coeff_ascPochhammer_self {S : Type*} [CommSemiring S] (n : ℕ) :
    coeff (ascPochhammer S n) n = 1 := by
  rw [coeff_ascPochhammer, if_pos le_rfl, Nat.stirlingFirst_self, Nat.cast_one]

/-- The rising factorials form a triangular family: no coefficients above the
degree. -/
theorem coeff_ascPochhammer_of_lt {S : Type*} [CommSemiring S] {n m : ℕ} (h : n < m) :
    coeff (ascPochhammer S n) m = 0 := by
  rw [coeff_ascPochhammer, if_neg (by omega)]

/-- **The two-sum recurrence of the first kind:**
`c(n+1,k+1) = ∑_{j ≤ n} c(n,j) C(j,k)`, the coefficient of `x^{k+1}` in
`x^{(n+1)} = x (x+1)^{(n)}`.

This is the single home of the identity: it is used both by the paired-sum
theorems (`StirlingSummations`) and by the reverse row recurrence
(`StirlingFirstReverse`), and neither of those modules imports the other. -/
theorem stirlingFirst_succ_succ_eq_sum_choose (n k : ℕ) :
    Nat.stirlingFirst (n + 1) (k + 1) =
      ∑ j ∈ Finset.range (n + 1), Nat.stirlingFirst n j * j.choose k := by
  have h : (ascPochhammer ℕ (n + 1)).coeff (k + 1) =
      (X * (ascPochhammer ℕ n).comp (X + 1)).coeff (k + 1) := by
    rw [ascPochhammer_succ_left]
  rw [coeff_X_mul, ascPochhammer_eq_sum_monomial_stirlingFirst ℕ n, Polynomial.sum_comp,
    finsetSum_coeff, coeff_ascPochhammer] at h
  simp only [monomial_comp, coeff_C_mul, coeff_X_add_one_pow, Nat.cast_id] at h
  split_ifs at h with hk
  · exact h
  · rw [Nat.stirlingFirst_eq_zero_of_lt (by omega)]
    symm
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]

/-- The row sum of the first-kind triangle: `∑_{k ≤ n} c(n,k) = n!`
(the rising factorial evaluated at `1`). -/
theorem sum_stirlingFirst_eq_factorial (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.stirlingFirst n k = n.factorial := by
  have h := congrArg (Polynomial.eval (1 : ℕ)) (ascPochhammer_eq_sum_monomial_stirlingFirst ℕ n)
  rw [ascPochhammer_nat_eq_ascFactorial, Nat.one_ascFactorial, eval_finsetSum] at h
  simpa [eval_monomial] using h.symm

/-! ### Second-kind numbers: powers in the factorial bases -/

/-- The one-step relation `X · (X)_k = (X)_{k+1} + k (X)_k` between consecutive
falling factorials. -/
theorem X_mul_descPochhammer {R : Type*} [CommRing R] (k : ℕ) :
    (X : R[X]) * descPochhammer R k =
      descPochhammer R (k + 1) + (k : R[X]) * descPochhammer R k := by
  rw [descPochhammer_succ_right]
  ring

/-- **Powers in the falling-factorial basis:**
`X^n = ∑_{k ≤ n} S(n,k) · X (X-1) ⋯ (X-k+1)`, over any commutative ring. -/
theorem X_pow_eq_sum_stirlingSecond_mul_descPochhammer (R : Type*) [CommRing R] (n : ℕ) :
    (X : R[X]) ^ n =
      ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : R[X]) * descPochhammer R k := by
  induction n with
  | zero => simp [descPochhammer_zero]
  | succ n ih =>
    have hsplit : (X : R[X]) ^ (n + 1)
        = ∑ k ∈ Finset.range (n + 1),
            (Nat.stirlingSecond n k : R[X]) * descPochhammer R (k + 1)
          + ∑ k ∈ Finset.range (n + 1),
            ((k : R[X]) * Nat.stirlingSecond n k) * descPochhammer R k := by
      rw [pow_succ', ih, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_left_comm, X_mul_descPochhammer]
      ring
    have hsecond : ∑ k ∈ Finset.range (n + 1),
          ((k : R[X]) * Nat.stirlingSecond n k) * descPochhammer R k
        = ∑ k ∈ Finset.range (n + 1),
          (((k + 1 : ℕ) : R[X]) * Nat.stirlingSecond n (k + 1)) * descPochhammer R (k + 1) := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ,
        Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self n)]
      simp
    have hrhs : ∑ k ∈ Finset.range (n + 2),
          (Nat.stirlingSecond (n + 1) k : R[X]) * descPochhammer R k
        = ∑ k ∈ Finset.range (n + 1),
            (((k + 1 : ℕ) : R[X]) * Nat.stirlingSecond n (k + 1)) * descPochhammer R (k + 1)
          + ∑ k ∈ Finset.range (n + 1),
            (Nat.stirlingSecond n k : R[X]) * descPochhammer R (k + 1) := by
      rw [Finset.sum_range_succ', Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul, add_zero,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.stirlingSecond_succ_succ]
      push_cast
      ring
    rw [hsplit, hsecond, hrhs, add_comm]

/-- Composition of a finite sum of polynomials with a fixed polynomial. -/
theorem finsetSum_comp {R : Type*} [CommSemiring R] {ι : Type*} (s : Finset ι)
    (g : ι → R[X]) (q : R[X]) :
    (∑ i ∈ s, g i).comp q = ∑ i ∈ s, (g i).comp q := by
  simp only [Polynomial.comp, eval₂_finsetSum]

/-- The falling factorial composed with `-X` is the rising factorial up to sign:
`(X)_k ∘ (-X) = (-1)^k · X (X+1) ⋯ (X+k-1)`. -/
theorem descPochhammer_comp_neg_X {R : Type*} [CommRing R] (k : ℕ) :
    (descPochhammer R k).comp (-X) = (-1) ^ k * ascPochhammer R k := by
  induction k with
  | zero => simp [descPochhammer_zero, ascPochhammer_zero]
  | succ k ih =>
    rw [descPochhammer_succ_right, ascPochhammer_succ_right, mul_comp, ih, sub_comp, X_comp,
      natCast_comp, pow_succ]
    ring

/-- The rising factorial composed with `-X` is the falling factorial up to sign:
`X (X+1) ⋯ (X+k-1) ∘ (-X) = (-1)^k · (X)_k`. -/
theorem ascPochhammer_comp_neg_X {R : Type*} [CommRing R] (k : ℕ) :
    (ascPochhammer R k).comp (-X) = (-1) ^ k * descPochhammer R k := by
  induction k with
  | zero => simp [descPochhammer_zero, ascPochhammer_zero]
  | succ k ih =>
    rw [ascPochhammer_succ_right, descPochhammer_succ_right, mul_comp, ih, add_comp, X_comp,
      natCast_comp, pow_succ]
    ring

/-- For `k ≤ n` the two sign conventions agree: `(-1)^(n-k) = (-1)^(n+k)`. -/
theorem neg_one_pow_sub_eq_neg_one_pow_add {R : Type*} [CommRing R] {k n : ℕ} (h : k ≤ n) :
    (-1 : R) ^ (n - k) = (-1) ^ (n + k) := by
  have hnk : n + k = (n - k) + 2 * k := by omega
  rw [hnk, pow_add, pow_mul]
  simp

/-- **Powers in the rising-factorial basis:**
`X^n = ∑_{k ≤ n} (-1)^(n-k) S(n,k) · X (X+1) ⋯ (X+k-1)`, over any commutative
ring. -/
theorem X_pow_eq_sum_stirlingSecond_mul_ascPochhammer (R : Type*) [CommRing R] (n : ℕ) :
    (X : R[X]) ^ n = ∑ k ∈ Finset.range (n + 1),
      ((-1) ^ (n - k) * Nat.stirlingSecond n k : R[X]) * ascPochhammer R k := by
  have h := congrArg (fun p : R[X] => p.comp (-X))
    (X_pow_eq_sum_stirlingSecond_mul_descPochhammer R n)
  simp only [X_pow_comp, finsetSum_comp, mul_comp, natCast_comp, descPochhammer_comp_neg_X] at h
  calc (X : R[X]) ^ n = (-1) ^ n * (-X) ^ n := by
        rw [neg_pow (X : R[X]) n, ← mul_assoc, ← mul_pow]
        simp
    _ = (-1) ^ n * ∑ k ∈ Finset.range (n + 1),
          (Nat.stirlingSecond n k : R[X]) * ((-1) ^ k * ascPochhammer R k) := by rw [h]
    _ = ∑ k ∈ Finset.range (n + 1),
          ((-1) ^ (n - k) * Nat.stirlingSecond n k : R[X]) * ascPochhammer R k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [neg_one_pow_sub_eq_neg_one_pow_add (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)),
          pow_add]
        ring

/-! ### Evaluated forms and the surjection formula -/

/-- `x^n = ∑_{k ≤ n} S(n,k) · x (x-1) ⋯ (x-k+1)` in any commutative ring. -/
theorem pow_eq_sum_stirlingSecond_mul_descPochhammer_eval {R : Type*} [CommRing R]
    (x : R) (n : ℕ) :
    x ^ n = ∑ k ∈ Finset.range (n + 1),
      (Nat.stirlingSecond n k : R) * (descPochhammer R k).eval x := by
  have h := congrArg (Polynomial.eval x) (X_pow_eq_sum_stirlingSecond_mul_descPochhammer R n)
  simpa only [eval_pow, eval_X, eval_finsetSum, eval_mul, eval_natCast] using h

/-- `m^n = ∑_{k ≤ n} S(n,k) · m^{\underline k}` for natural numbers. -/
theorem pow_eq_sum_stirlingSecond_mul_descFactorial (m n : ℕ) :
    m ^ n = ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k * m.descFactorial k := by
  have h := pow_eq_sum_stirlingSecond_mul_descPochhammer_eval (R := ℤ) (m : ℤ) n
  simp only [descPochhammer_eval_eq_descFactorial] at h
  exact_mod_cast h

/-- `m^n = ∑_{k ≤ n} S(n,k) k! C(m,k)`: every map `[n] → [m]` is a surjection
onto its image, an ordered choice of `k` used values. -/
theorem pow_eq_sum_stirlingSecond_mul_factorial_mul_choose (m n : ℕ) :
    m ^ n = ∑ k ∈ Finset.range (n + 1),
      Nat.stirlingSecond n k * (k.factorial * m.choose k) := by
  simp only [← Nat.descFactorial_eq_factorial_mul_choose]
  exact pow_eq_sum_stirlingSecond_mul_descFactorial m n

/-- **The surjection formula** (inclusion–exclusion for the second kind), as an
identity in `ℤ`: `k! S(n,k) = ∑_{j ≤ k} (-1)^(k-j) C(k,j) j^n`. -/
theorem factorial_mul_stirlingSecond_eq_sum (n k : ℕ) :
    (k.factorial * Nat.stirlingSecond n k : ℤ) =
      ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - j) * k.choose j * (j : ℤ) ^ n := by
  have hb : ∀ m : ℕ, ((m : ℤ) ^ n) =
      ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℤ) * (j.factorial * Nat.stirlingSecond n j : ℤ) := by
    intro m
    have hL : ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k * (k.factorial * m.choose k)
        = ∑ k ∈ Finset.range (n + m + 1),
            Nat.stirlingSecond n k * (k.factorial * m.choose k) := by
      apply Finset.sum_subset (Finset.range_mono (show n + 1 ≤ n + m + 1 by omega))
      intro k _ hk
      have hnk : n < k := by
        rw [Finset.mem_range, not_lt] at hk
        omega
      rw [Nat.stirlingSecond_eq_zero_of_lt hnk, zero_mul]
    have hR : ∑ j ∈ Finset.range (m + 1), m.choose j * (j.factorial * Nat.stirlingSecond n j)
        = ∑ j ∈ Finset.range (n + m + 1),
            m.choose j * (j.factorial * Nat.stirlingSecond n j) := by
      apply Finset.sum_subset (Finset.range_mono (show m + 1 ≤ n + m + 1 by omega))
      intro j _ hj
      have hmj : m < j := by
        rw [Finset.mem_range, not_lt] at hj
        omega
      rw [Nat.choose_eq_zero_of_lt hmj, zero_mul]
    have hnat : m ^ n =
        ∑ j ∈ Finset.range (m + 1), m.choose j * (j.factorial * Nat.stirlingSecond n j) := by
      rw [pow_eq_sum_stirlingSecond_mul_factorial_mul_choose, hL, hR]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    exact_mod_cast hnat
  exact binomial_inversion_ring (fun j => (j.factorial * Nat.stirlingSecond n j : ℤ))
    (fun m => (m : ℤ) ^ n) hb k

/-- The surjection formula in divided form over `ℚ`:
`S(n,k) = (1/k!) ∑_{j ≤ k} (-1)^(k-j) C(k,j) j^n`. -/
theorem stirlingSecond_eq_sum_div_factorial (n k : ℕ) :
    (Nat.stirlingSecond n k : ℚ) =
      (∑ j ∈ Finset.range (k + 1), (-1 : ℚ) ^ (k - j) * k.choose j * (j : ℚ) ^ n) /
        k.factorial := by
  have h := congrArg (Int.cast : ℤ → ℚ) (factorial_mul_stirlingSecond_eq_sum n k)
  push_cast at h
  rw [eq_div_iff (Nat.cast_ne_zero.mpr k.factorial_ne_zero), mul_comm]
  exact h

/-! ### Orthogonality of the two kinds -/

/-- **Inverse matrices, first order:** `∑_{j ≤ n} S(n,j) s(j,k) = δ_{nk}`.  The
terms with `j < k` vanish, so the sum may equally be taken over `k ≤ j ≤ n`. -/
theorem sum_range_stirlingSecond_mul_signedStirlingFirst (n k : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (Nat.stirlingSecond n j : ℤ) * signedStirlingFirst j k) =
      if n = k then 1 else 0 := by
  have hcoeff : ∀ j, coeff ((Nat.stirlingSecond n j : ℤ[X]) * descPochhammer ℤ j) k
      = (Nat.stirlingSecond n j : ℤ) * signedStirlingFirst j k := by
    intro j
    rw [← C_eq_natCast, coeff_C_mul, coeff_descPochhammer]
    split_ifs with hkj
    · simp
    · rw [signedStirlingFirst_eq_zero_of_lt (show j < k by omega), mul_zero]
  have h := congrArg (fun p : ℤ[X] => coeff p k)
    (X_pow_eq_sum_stirlingSecond_mul_descPochhammer ℤ n)
  simp only [coeff_X_pow, finsetSum_coeff, hcoeff] at h
  rw [← h]
  by_cases hnk : n = k
  · subst hnk
    simp
  · rw [if_neg hnk, if_neg (Ne.symm hnk)]

/-- The first-order inverse relation over the interval `Icc k n`. -/
theorem sum_Icc_stirlingSecond_mul_signedStirlingFirst (n k : ℕ) :
    (∑ j ∈ Finset.Icc k n, (Nat.stirlingSecond n j : ℤ) * signedStirlingFirst j k) =
      if n = k then 1 else 0 := by
  rw [← sum_range_stirlingSecond_mul_signedStirlingFirst n k]
  rcases lt_or_ge n k with hnk | hkn
  · rw [Finset.Icc_eq_empty_of_lt hnk, Finset.sum_empty]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j < n + 1 := Finset.mem_range.mp hj
    rw [signedStirlingFirst_eq_zero_of_lt (show j < k by omega), mul_zero]
  · apply Finset.sum_subset
    · intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_range]
      omega
    · intro j hj hj'
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Icc] at hj'
      rw [signedStirlingFirst_eq_zero_of_lt (show j < k by omega), mul_zero]

/-- **Inverse matrices, second order:** `∑_{j ∈ Icc k n} s(n,j) S(j,k) = δ_{nk}`,
obtained from the first order by the kernel commutation theorem. -/
theorem sum_Icc_signedStirlingFirst_mul_stirlingSecond (n k : ℕ) :
    (∑ j ∈ Finset.Icc k n, signedStirlingFirst n j * (Nat.stirlingSecond j k : ℤ)) =
      if n = k then 1 else 0 :=
  lowerTriangular_orthogonal_comm (fun n j => (Nat.stirlingSecond n j : ℤ))
    (fun j k => signedStirlingFirst j k) sum_Icc_stirlingSecond_mul_signedStirlingFirst n k

/-- The second-order inverse relation with the sum over `j ≤ n`. -/
theorem sum_range_signedStirlingFirst_mul_stirlingSecond (n k : ℕ) :
    (∑ j ∈ Finset.range (n + 1), signedStirlingFirst n j * (Nat.stirlingSecond j k : ℤ)) =
      if n = k then 1 else 0 := by
  rw [← sum_Icc_signedStirlingFirst_mul_stirlingSecond n k]
  rcases lt_or_ge n k with hnk | hkn
  · rw [Finset.Icc_eq_empty_of_lt hnk, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j < n + 1 := Finset.mem_range.mp hj
    rw [Nat.stirlingSecond_eq_zero_of_lt (show j < k by omega), Nat.cast_zero, mul_zero]
  · symm
    apply Finset.sum_subset
    · intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_range]
      omega
    · intro j hj hj'
      rw [Finset.mem_range] at hj
      rw [Finset.mem_Icc] at hj'
      rw [Nat.stirlingSecond_eq_zero_of_lt (show j < k by omega), Nat.cast_zero, mul_zero]

/-! ### The Stirling transform and its inverse -/

section Transform

variable {M : Type*} [AddCommGroup M]

/-- **Stirling inversion.**  If `g n = ∑_{k ≤ n} S(n,k) • f k` for every `n`,
then `f n = ∑_{k ≤ n} s(n,k) • g k`. -/
theorem stirling_inversion (f g : ℕ → M)
    (h : ∀ n, g n = ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : ℤ) • f k) (n : ℕ) :
    f n = ∑ k ∈ Finset.range (n + 1), signedStirlingFirst n k • g k := by
  have hg : g = lowerTriangularTransform (fun n k => (Nat.stirlingSecond n k : ℤ)) f := by
    funext n
    rw [h n, lowerTriangularTransform, range_succ_eq_Icc_zero]
  have hcomp := lowerTriangularTransform_comp (R := ℤ) (fun n k => signedStirlingFirst n k)
    (fun n k => (Nat.stirlingSecond n k : ℤ)) sum_Icc_signedStirlingFirst_mul_stirlingSecond f
  rw [← hg] at hcomp
  rw [range_succ_eq_Icc_zero]
  exact (congrFun hcomp n).symm

/-- The converse of Stirling inversion: if `f n = ∑_{k ≤ n} s(n,k) • g k` for
every `n`, then `g n = ∑_{k ≤ n} S(n,k) • f k`. -/
theorem stirling_inversion_symm (f g : ℕ → M)
    (h : ∀ n, f n = ∑ k ∈ Finset.range (n + 1), signedStirlingFirst n k • g k) (n : ℕ) :
    g n = ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : ℤ) • f k := by
  have hf : f = lowerTriangularTransform (fun n k => signedStirlingFirst n k) g := by
    funext n
    rw [h n, lowerTriangularTransform, range_succ_eq_Icc_zero]
  have hcomp := lowerTriangularTransform_comp_symm (R := ℤ) (fun n k => signedStirlingFirst n k)
    (fun n k => (Nat.stirlingSecond n k : ℤ)) sum_Icc_signedStirlingFirst_mul_stirlingSecond g
  rw [← hf] at hcomp
  rw [range_succ_eq_Icc_zero]
  exact (congrFun hcomp n).symm

/-- The Stirling transform and its inverse as an equivalence of sequence
relations. -/
theorem stirling_inversion_iff (f g : ℕ → M) :
    (∀ n, g n = ∑ k ∈ Finset.range (n + 1), (Nat.stirlingSecond n k : ℤ) • f k) ↔
      (∀ n, f n = ∑ k ∈ Finset.range (n + 1), signedStirlingFirst n k • g k) :=
  ⟨fun h => stirling_inversion f g h, fun h => stirling_inversion_symm f g h⟩

end Transform

/-! ### Power sums through the factorial basis -/

/-- The hockey-stick identity with a `range` sum: `∑_{i ≤ N} C(i,k) = C(N+1,k+1)`. -/
theorem sum_range_choose_eq_choose_succ_succ (N k : ℕ) :
    ∑ i ∈ Finset.range (N + 1), i.choose k = (N + 1).choose (k + 1) := by
  rw [← Nat.sum_Icc_choose N k]
  symm
  apply Finset.sum_subset
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_range]
    omega
  · intro i hi hi'
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc] at hi'
    exact Nat.choose_eq_zero_of_lt (by omega)

/-- **Power sums by basis adaptation:**
`∑_{i=0}^{N} i^m = ∑_{k ≤ m} S(m,k) · k! · C(N+1, k+1)`, the factorial-basis
form of Faulhaber's sum (`k! C(N+1,k+1) = (N+1)^{\underline{k+1}} / (k+1)`). -/
theorem sum_range_pow_eq_sum_stirlingSecond (N m : ℕ) :
    ∑ i ∈ Finset.range (N + 1), i ^ m =
      ∑ k ∈ Finset.range (m + 1),
        Nat.stirlingSecond m k * (k.factorial * (N + 1).choose (k + 1)) := by
  calc ∑ i ∈ Finset.range (N + 1), i ^ m
      = ∑ i ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (m + 1),
          Nat.stirlingSecond m k * (k.factorial * i.choose k) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact pow_eq_sum_stirlingSecond_mul_factorial_mul_choose i m
    _ = ∑ k ∈ Finset.range (m + 1), Nat.stirlingSecond m k *
          (k.factorial * ∑ i ∈ Finset.range (N + 1), i.choose k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sum_range_choose_eq_choose_succ_succ]

end Fabius
