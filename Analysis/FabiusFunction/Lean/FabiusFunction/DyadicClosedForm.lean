import FabiusFunction.DyadicCorrectness
import FabiusFunction.MomentPowerSeries
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic.FieldSimp

/-!
# Closed-form dyadic recurrence for the Fabius function

This module proves the exact Taylor-block identity behind the executable
bit recursion.  It combines Thue--Morse cancellation with a polynomial kernel
refinement law, identifies the inverse-power lookup table, and concludes that
`fabiusDyadicUnit` agrees with the closed formula `fabiusDyadic` on `[0, 1]`.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-- Choosing disjoint blocks of sizes `p` and `j` out of `n` elements gives
the same count in either order.  This symmetry is what lets the binomial
coefficients be re-indexed in `dyadicKernelPolynomial_hasseDeriv`. -/
lemma choose_mul_choose_disjoint (n p j : ℕ) :
    Nat.choose n p * Nat.choose (n - p) j =
      Nat.choose n j * Nat.choose (n - j) p := by
  have hp := Nat.choose_mul (n := n) (k := p + j) (s := p) (by omega : p ≤ p + j)
  have hj := Nat.choose_mul (n := n) (k := p + j) (s := j) (by omega : j ≤ p + j)
  have hsym : Nat.choose (p + j) p = Nat.choose (p + j) j :=
    Nat.choose_symm_of_eq_add rfl
  calc
    _ = Nat.choose n (p + j) * Nat.choose (p + j) p := by
      simpa using hp.symm
    _ = Nat.choose n (p + j) * Nat.choose (p + j) j := by rw [hsym]
    _ = _ := by simpa [add_comm] using hj

/-- Triangular numbers split additively: `Nat.choose (m + j + 1) 2` equals
`Nat.choose (m + 1) 2 + m * j + Nat.choose (j + 1) 2`.  This is the exponent
bookkeeping behind the power of two in `dyadicScale_choose_taylor`. -/
lemma choose_add_succ_two (m j : ℕ) :
    Nat.choose (m + j + 1) 2 =
      Nat.choose (m + 1) 2 + m * j + Nat.choose (j + 1) 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show m + (j + 1) + 1 = (m + j + 1) + 1 by omega,
        show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
      rw [ih]
      have hjchoose : Nat.choose (j + 2) 2 = Nat.choose (j + 1) 2 + (j + 1) := by
        rw [show j + 2 = (j + 1) + 1 by omega,
          show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]
      rw [hjchoose]
      simp [Nat.choose_one_right]
      ring

/-- Closed form for a triangular number:
`2 * Nat.choose (j + 1) 2 = j * (j + 1)`. -/
lemma two_mul_choose_succ_two (j : ℕ) :
    2 * Nat.choose (j + 1) 2 = j * (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hchoose : Nat.choose (j + 2) 2 = Nat.choose (j + 1) 2 + (j + 1) := by
        rw [show j + 2 = (j + 1) + 1 by omega,
          show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]
      rw [hchoose]
      rw [Nat.mul_add, ih]
      ring

/-- Splits a `Fin (m + n)` sum into its first `m` terms and the `n` terms
after them, reindexed by `m + i`.  The `Fin`-indexed form of
`Finset.sum_range_add`, used to peel off a leading dyadic block in
`thueMorse_sum_split`. -/
theorem sum_fin_add {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m n : ℕ) :
    (∑ i : Fin (m + n), f i.val) =
      (∑ i : Fin m, f i.val) + ∑ i : Fin n, f (m + i.val) := by
  rw [Fin.sum_univ_eq_sum_range f (m + n), Fin.sum_univ_eq_sum_range f m,
    Fin.sum_univ_eq_sum_range (fun i => f (m + i)) n]
  exact Finset.sum_range_add f m n

/-- Pairs a `Fin (2 * a)` sum into `a` consecutive two-term blocks
`f (2 j) + f (2 j + 1)`.  This is the index bookkeeping for the halving step
`thueMorse_sum_two_mul`. -/
theorem sum_fin_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a : ℕ) :
    (∑ i : Fin (2 * a), f i.val) =
      ∑ j : Fin a, (f (2 * j.val) + f (2 * j.val + 1)) := by
  rw [Fin.sum_univ_eq_sum_range f (2 * a),
    Fin.sum_univ_eq_sum_range (fun j => f (2 * j) + f (2 * j + 1)) a]
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      rw [Finset.sum_range_succ]
      simp
      rw [Finset.sum_range_succ]

/-- Setting a fresh leading binary bit raises the digit sum by one:
`binaryWeight (2 ^ b + h) = binaryWeight h + 1` for `h < 2 ^ b`.  The
hypothesis is essential -- it is what makes the new bit disjoint from the
digits of `h`.  This is the arithmetic behind `thueMorseSign_add_pow_two`. -/
theorem binaryWeight_add_pow_two (b h : ℕ) (hh : h < 2 ^ b) :
    binaryWeight (2 ^ b + h) = binaryWeight h + 1 := by
  have hlen : (Nat.digits 2 h).length ≤ b :=
    (Nat.digits_length_le_iff Nat.one_lt_two h).2 hh
  have hdigits :=
    Nat.digits_append_zeroes_append_digits (b := 2)
      (k := b - (Nat.digits 2 h).length) (m := 1) (n := h)
      Nat.one_lt_two (by decide)
  rw [Nat.add_sub_of_le hlen] at hdigits
  have hone : Nat.digits 2 1 = [1] := by norm_num [Nat.digits_of_lt]
  simp only [hone, mul_one] at hdigits
  rw [add_comm] at hdigits
  rw [binaryWeight, binaryWeight, ← hdigits]
  simp

/-- Appending a zero binary digit leaves the digit sum unchanged. -/
@[simp] theorem binaryWeight_two_mul (h : ℕ) :
    binaryWeight (2 * h) = binaryWeight h := by
  cases h with
  | zero => simp [binaryWeight]
  | succ h =>
      rw [binaryWeight, binaryWeight,
        Nat.digits_base_mul Nat.one_lt_two (by positivity : 0 < h + 1)]
      simp

/-- Appending a one binary digit raises the digit sum by one. -/
@[simp] theorem binaryWeight_two_mul_add_one (h : ℕ) :
    binaryWeight (2 * h + 1) = binaryWeight h + 1 := by
  rw [binaryWeight, binaryWeight]
  have hdigits := Nat.digits_add 2 Nat.one_lt_two 1 h (by decide) (Or.inl (by decide))
  rw [add_comm] at hdigits
  rw [hdigits]
  simp [add_comm]

/-- The Thue--Morse sign is invariant under doubling the index. -/
@[simp] theorem thueMorseSign_two_mul (h : ℕ) :
    thueMorseSign (2 * h) = thueMorseSign h := by
  simp [thueMorseSign]

/-- The Thue--Morse sign flips between an even index and its successor. -/
@[simp] theorem thueMorseSign_two_mul_add_one (h : ℕ) :
    thueMorseSign (2 * h + 1) = -thueMorseSign h := by
  simp [thueMorseSign, pow_succ]

/-- The signed Thue--Morse sequence is a character of bitwise xor. -/
theorem thueMorseSign_xor (a b : ℕ) :
    thueMorseSign (a ^^^ b) = thueMorseSign a * thueMorseSign b := by
  induction a using Nat.binaryRec generalizing b with
  | zero => simp [thueMorseSign, binaryWeight]
  | bit ba a ih =>
      refine Nat.bitCasesOn b ?_
      intro bb b
      rw [Nat.xor_bit]
      cases ba <;> cases bb <;> simp [ih]

/-- Reflecting an index in a dyadic block complements its first `k` binary
digits and multiplies its Thue--Morse sign by `(-1)^k`. -/
theorem thueMorseSign_dyadic_complement
    (k r : ℕ) (hr : r < 2 ^ k) :
    thueMorseSign (2 ^ k - 1 - r) =
      (-1 : ℤ) ^ k * thueMorseSign r := by
  induction k generalizing r with
  | zero =>
      have hr0 : r = 0 := by omega
      subst r
      norm_num [thueMorseSign, binaryWeight]
  | succ k ih =>
      rcases Nat.even_or_odd r with heven | hodd
      · rcases heven with ⟨s, hs⟩
        have hrform : r = 2 * s := by omega
        have hslt : s < 2 ^ k := by
          rw [pow_succ] at hr
          omega
        have hreflect :
            2 ^ (k + 1) - 1 - r =
              2 * (2 ^ k - 1 - s) + 1 := by
          rw [pow_succ]
          omega
        rw [hreflect, thueMorseSign_two_mul_add_one,
          ih s hslt, hrform, thueMorseSign_two_mul, pow_succ]
        ring
      · rcases hodd with ⟨s, hs⟩
        have hrform : r = 2 * s + 1 := by omega
        have hslt : s < 2 ^ k := by
          rw [pow_succ] at hr
          omega
        have hreflect :
            2 ^ (k + 1) - 1 - r =
              2 * (2 ^ k - 1 - s) := by
          rw [pow_succ]
          omega
        rw [hreflect, thueMorseSign_two_mul,
          ih s hslt, hrform, thueMorseSign_two_mul_add_one, pow_succ]
        ring

/-- Halving a signed Thue--Morse sum: a sum of `thueMorseSign i * f i` over
`Fin (2 * a)` collapses to a sum of `thueMorseSign j * (f (2 j) - f (2 j + 1))`
over `Fin a`, because the sign flips within each adjacent pair.  This is the
step that converts the kernel refinement law into
`fabiusDyadic_refine_of_kernel`. -/
theorem thueMorse_sum_two_mul (a : ℕ) (f : ℕ → ℚ) :
    (∑ i : Fin (2 * a), (thueMorseSign i.val : ℚ) * f i.val) =
      ∑ j : Fin a, (thueMorseSign j.val : ℚ) *
        (f (2 * j.val) - f (2 * j.val + 1)) := by
  let g : ℕ → ℚ := fun i => (thueMorseSign i : ℚ) * f i
  change (∑ i : Fin (2 * a), g i.val) =
    ∑ j : Fin a, (thueMorseSign j.val : ℚ) *
      (f (2 * j.val) - f (2 * j.val + 1))
  rw [sum_fin_two_mul g]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [g]
  simp only [thueMorseSign_two_mul, thueMorseSign_two_mul_add_one]
  push_cast
  ring

/-- The signed power sum `∑_{h < 2 ^ b} thueMorseSign h * h ^ d` over one
complete dyadic Thue--Morse block. -/
private def thuePowerSum (b d : ℕ) : ℚ :=
  ∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) * (h.val : ℚ) ^ d

/-- Doubling the block length expresses `thuePowerSum (b + 1) d` through the
half-length block in degrees strictly below `d`: the degree-`d` terms of the
two halves cancel, which is why the range stops at `d` and why the whole sum
picks up a minus sign.  This is the induction step of
`thuePowerSum_eq_zero_of_lt`, and it is re-exported under local names by
`ThueMorsePrefix` and `FabiusUniformSpline`. -/
lemma thuePowerSum_succ (b d : ℕ) :
    thuePowerSum (b + 1) d =
      -(∑ k ∈ Finset.range d,
          (Nat.choose d k : ℚ) * (2 : ℚ) ^ k * thuePowerSum b k) := by
  rw [thuePowerSum, pow_succ', mul_comm]
  rw [show 2 ^ b * 2 = 2 * 2 ^ b by omega]
  change
    (∑ i : Fin (2 * 2 ^ b),
      (thueMorseSign i.val : ℚ) * (i.val : ℚ) ^ d) = _
  let f : ℕ → ℚ := fun i => (i : ℚ) ^ d
  change
    (∑ i : Fin (2 * 2 ^ b),
      (thueMorseSign i.val : ℚ) * f i.val) = _
  rw [thueMorse_sum_two_mul (2 ^ b) f]
  have hpoint (j : ℕ) :
      ((2 * j : ℕ) : ℚ) ^ d - ((2 * j + 1 : ℕ) : ℚ) ^ d =
        -(∑ k ∈ Finset.range d,
          (Nat.choose d k : ℚ) * (2 : ℚ) ^ k * (j : ℚ) ^ k) := by
    push_cast
    rw [add_pow, Finset.sum_range_succ]
    simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one]
    rw [mul_pow]
    ring_nf
  simp only [f]
  simp_rw [hpoint]
  calc
    (∑ j : Fin (2 ^ b), (thueMorseSign j.val : ℚ) *
        -(∑ k ∈ Finset.range d,
          (Nat.choose d k : ℚ) * (2 : ℚ) ^ k * (j.val : ℚ) ^ k)) =
      -(∑ j : Fin (2 ^ b), ∑ k ∈ Finset.range d,
        (thueMorseSign j.val : ℚ) *
          ((Nat.choose d k : ℚ) * (2 : ℚ) ^ k * (j.val : ℚ) ^ k)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_neg, neg_inj, Finset.mul_sum]
    _ = -(∑ k ∈ Finset.range d, ∑ j : Fin (2 ^ b),
        (thueMorseSign j.val : ℚ) *
          ((Nat.choose d k : ℚ) * (2 : ℚ) ^ k * (j.val : ℚ) ^ k)) := by
        rw [Finset.sum_comm]
    _ = _ := by
      apply congrArg Neg.neg
      apply Finset.sum_congr rfl
      intro k hk
      rw [thuePowerSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Prouhet cancellation: a complete Thue--Morse block of length `2 ^ b`
annihilates every monomial of degree `d < b`.  The hypothesis is exactly
`d < b`; at `d = b` the sum is nonzero, with the explicit value computed in
`ThueMorsePrefix.thueMorsePowerSum_self`. -/
lemma thuePowerSum_eq_zero_of_lt (b d : ℕ) (hd : d < b) :
    thuePowerSum b d = 0 := by
  induction b generalizing d with
  | zero => omega
  | succ b ih =>
      rw [thuePowerSum_succ]
      rw [Finset.sum_eq_zero]
      · simp
      · intro k hk
        have hklt : k < d := Finset.mem_range.mp hk
        rw [ih k (hklt.trans_le (by omega : d ≤ b))]
        ring

/-- Prouhet cancellation for an arbitrary affine argument: for `d < b` the
signed sum of `(x + y * h) ^ d` over a complete block `h < 2 ^ b` vanishes, for
every `x` and `y`.  Expanding the binomial reduces it to
`thuePowerSum_eq_zero_of_lt` in each degree. -/
lemma thueMorse_affine_power_sum_eq_zero (b d : ℕ) (hd : d < b)
    (x y : ℚ) :
    (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
      (x + y * (h.val : ℚ)) ^ d) = 0 := by
  simp_rw [add_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  have hdegree : d - k < b := (Nat.sub_le d k).trans_lt hd
  have hinner :
      (∑ h : Fin (2 ^ b),
        (thueMorseSign h.val : ℚ) *
          (x ^ k * (y * (h.val : ℚ)) ^ (d - k) * (Nat.choose d k : ℚ))) =
        (x ^ k * y ^ (d - k) * (Nat.choose d k : ℚ)) *
          thuePowerSum b (d - k) := by
    rw [thuePowerSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [mul_pow]
    ring
  rw [hinner, thuePowerSum_eq_zero_of_lt b (d - k) hdegree, mul_zero]

/-- Adding a fresh leading bit flips the Thue--Morse sign:
`thueMorseSign (2 ^ b + h) = -thueMorseSign h` for `h < 2 ^ b`.  The corpus
uses this whenever a dyadic block is reflected onto its translate. -/
theorem thueMorseSign_add_pow_two (b h : ℕ) (hh : h < 2 ^ b) :
    thueMorseSign (2 ^ b + h) = -thueMorseSign h := by
  rw [thueMorseSign, thueMorseSign, binaryWeight_add_pow_two b h hh, pow_succ]
  ring

/-- Splits a signed sum over `2 ^ b + r` indices, with `r ≤ 2 ^ b`, as the
complete leading block minus the signed sum over the `r` translated indices;
the minus sign is `thueMorseSign_add_pow_two`.  This is the identity behind
`fabiusDyadic_add_remainder_eq_block`. -/
theorem thueMorse_sum_split (b r : ℕ) (hr : r ≤ 2 ^ b) (f : ℕ → ℚ) :
    (∑ i : Fin (2 ^ b + r), (thueMorseSign i.val : ℚ) * f i.val) =
      (∑ i : Fin (2 ^ b), (thueMorseSign i.val : ℚ) * f i.val) -
        ∑ j : Fin r, (thueMorseSign j.val : ℚ) * f (2 ^ b + j.val) := by
  let g : ℕ → ℚ := fun i => (thueMorseSign i : ℚ) * f i
  change (∑ i : Fin (2 ^ b + r), g i.val) =
    (∑ i : Fin (2 ^ b), g i.val) -
      ∑ j : Fin r, (thueMorseSign j.val : ℚ) * f (2 ^ b + j.val)
  rw [sum_fin_add g]
  rw [sub_eq_add_neg, add_right_inj, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j.val < 2 ^ b := j.isLt.trans_le hr
  simp only [g]
  rw [thueMorseSign_add_pow_two b j.val hjlt]
  push_cast
  ring

/-- The normalization of equation (32) at grid exponent `n`, namely
`2 ^ (-Nat.choose (n + 1) 2) / n !`.  The negative exponent is an integer
power, so this is the exact rational prefactor, not a truncation. -/
private def dyadicScale (n : ℕ) : ℚ :=
  (2 : ℚ) ^ (-(Nat.choose (n + 1) 2 : ℤ)) / n.factorial

/-- The polynomial kernel of equation (32): `∑_{2 k ≤ n}` of
`Nat.choose n (2 k) * x ^ (n - 2 k) * moment k`.  Only even binomial indices
occur, so the moments enter at index `k` while the power of `x` keeps the
parity of `n`.  Multiplying the signed sum of
`thueMorseSign h * dyadicKernel n (2 a - 2 h - 1)` over `h < a` by
`dyadicScale n` gives `fabiusDyadic n a`. -/
private def dyadicKernel (n : ℕ) (x : ℚ) : ℚ :=
  ∑ k : Fin (n / 2 + 1),
    (Nat.choose n (2 * k.val) : ℚ) * x ^ (n - 2 * k.val) * moment k.val

/-- Rewrites the `Fin`-indexed kernel sum as a sum over
`Finset.range (n / 2 + 1)`, the form the polynomial computations below use. -/
lemma dyadicKernel_eq_sum_range (n : ℕ) (x : ℚ) :
    dyadicKernel n x =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (Nat.choose n (2 * k) : ℚ) * x ^ (n - 2 * k) * moment k := by
  let g : ℕ → ℚ := fun k =>
    (Nat.choose n (2 * k) : ℚ) * x ^ (n - 2 * k) * moment k
  change (∑ k : Fin (n / 2 + 1), g k.val) = _
  rw [Fin.sum_univ_eq_sum_range g (n / 2 + 1)]

/-- The kernel `dyadicKernel n` as a formal polynomial over `ℚ`, built from
monomials of degree `n - 2 k`.  Working with the polynomial rather than
the function is what makes the derivative and Taylor arguments below
available. -/
private noncomputable def dyadicKernelPolynomial (n : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    Polynomial.monomial (n - 2 * k)
      ((Nat.choose n (2 * k) : ℚ) * moment k)

/-- The kernel polynomial evaluates to the kernel function.  This is the
bridge that lets the refinement law be proved as a polynomial identity and
then transported back to values. -/
lemma dyadicKernelPolynomial_eval (n : ℕ) (x : ℚ) :
    (dyadicKernelPolynomial n).eval x = dyadicKernel n x := by
  rw [dyadicKernelPolynomial, dyadicKernel,
    Polynomial.eval_finsetSum (Finset.range (n / 2 + 1))]
  let g : ℕ → ℚ := fun k =>
    (Nat.choose n (2 * k) : ℚ) * x ^ (n - 2 * k) * moment k
  change (∑ k ∈ Finset.range (n / 2 + 1),
      Polynomial.eval x (Polynomial.monomial (n - 2 * k)
        ((Nat.choose n (2 * k) : ℚ) * moment k))) =
    ∑ k : Fin (n / 2 + 1), g k.val
  rw [Fin.sum_univ_eq_sum_range g (n / 2 + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_monomial]
  ring

/-- The `j`-th Hasse derivative of the kernel polynomial, for `j ≤ n`, is
`Nat.choose n j` times the kernel polynomial of index `n - j`.  This closure
of the kernel family under differentiation is what gives the finite Taylor
expansion `dyadicKernel_taylor`. -/
lemma dyadicKernelPolynomial_hasseDeriv (n j : ℕ) (hj : j ≤ n) :
    Polynomial.hasseDeriv j (dyadicKernelPolynomial n) =
      Polynomial.C (Nat.choose n j : ℚ) * dyadicKernelPolynomial (n - j) := by
  rw [dyadicKernelPolynomial, map_sum]
  rw [dyadicKernelPolynomial, Finset.mul_sum]
  simp only [Polynomial.hasseDeriv_monomial, Polynomial.C_mul_monomial]
  have hsmall : (n - j) / 2 + 1 ≤ n / 2 + 1 := by
    exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le n j)) 1
  symm
  apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono hsmall)
  · intro k hk
    have hkbig : k < n / 2 + 1 := Finset.mem_range.mp (Finset.mem_sdiff.mp hk).1
    have hknsmall : ¬ k < (n - j) / 2 + 1 := by
      simpa only [Finset.mem_range] using (Finset.mem_sdiff.mp hk).2
    have hdivlt : (n - j) / 2 < k := by omega
    have htwok : n - j < k * 2 :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp hdivlt
    have hlt : n - 2 * k < j := by omega
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp
  · intro k hk
    have hk_le_div : k ≤ (n - j) / 2 := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
    have htwok : k * 2 ≤ n - j :=
      (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hk_le_div
    have htwok' : 2 * k ≤ n - j := by omega
    have hexponent : n - 2 * k - j = n - j - 2 * k := by omega
    have hcoefficient := choose_mul_choose_disjoint n (2 * k) j
    rw [hexponent]
    congr 1
    have hcoefficientQ :
        (Nat.choose n j : ℚ) * Nat.choose (n - j) (2 * k) =
          (Nat.choose (n - 2 * k) j : ℚ) * Nat.choose n (2 * k) := by
      have hnat : Nat.choose n j * Nat.choose (n - j) (2 * k) =
          Nat.choose (n - 2 * k) j * Nat.choose n (2 * k) := by
        simpa [mul_comm] using hcoefficient.symm
      exact_mod_cast hnat
    calc
      _ = ((Nat.choose n j : ℚ) * Nat.choose (n - j) (2 * k)) * moment k := by ring
      _ = ((Nat.choose (n - 2 * k) j : ℚ) * Nat.choose n (2 * k)) * moment k := by
        rw [hcoefficientQ]
      _ = _ := by ring

/-- The kernel polynomial has degree at most `n`, so its Taylor expansion
terminates after `n + 1` terms. -/
lemma dyadicKernelPolynomial_natDegree_le (n : ℕ) :
    (dyadicKernelPolynomial n).natDegree ≤ n := by
  rw [dyadicKernelPolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.sub_le n (2 * k))

/-- Finite Taylor expansion of the kernel: `dyadicKernel n (x + y)` equals
`∑_{j ≤ n} Nat.choose n j * dyadicKernel (n - j) x * y ^ j`.  The identity is
exact, not an approximation, because the kernel is a polynomial of degree at
most `n`; `dyadicBlock_expand` sums it over a Thue--Morse block. -/
lemma dyadicKernel_taylor (n : ℕ) (x y : ℚ) :
    dyadicKernel n (x + y) =
      ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j : ℚ) * dyadicKernel (n - j) x * y ^ j := by
  let p := dyadicKernelPolynomial n
  have hpdeg : p.natDegree < n + 1 := by
    exact (dyadicKernelPolynomial_natDegree_le n).trans_lt (Nat.lt_succ_self n)
  have htdeg : (Polynomial.taylor x p).natDegree < n + 1 := by
    rw [Polynomial.natDegree_taylor]
    exact hpdeg
  calc
    dyadicKernel n (x + y) = p.eval (y + x) := by
      change dyadicKernel n (x + y) =
        (dyadicKernelPolynomial n).eval (y + x)
      rw [add_comm, dyadicKernelPolynomial_eval]
    _ = (Polynomial.taylor x p).eval y := by
      rw [Polynomial.taylor_eval]
    _ = ∑ j ∈ Finset.range (n + 1),
          (Polynomial.taylor x p).coeff j * y ^ j :=
      Polynomial.eval_eq_sum_range' htdeg y
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ n := by simpa using Finset.mem_range.mp hj
      rw [Polynomial.taylor_coeff,
        show p = dyadicKernelPolynomial n by rfl,
        dyadicKernelPolynomial_hasseDeriv n j hjle,
        Polynomial.eval_mul, Polynomial.eval_C,
        dyadicKernelPolynomial_eval]

/-- Value of an odd-index kernel at `x = 1`:
`dyadicKernel (2 q + 1) 1 = (2 q + 1) * 2 ^ (2 q) * moment q`.  The moment
recurrence `moment_succ` is what collapses the sum to this single term.  Used
to evaluate the refinement defect in `dyadicKernelPolynomial_refinement`. -/
lemma dyadicKernel_odd_one (q : ℕ) :
    dyadicKernel (2 * q + 1) 1 =
      ((2 * q + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (2 * q) * moment q := by
  cases q with
  | zero => norm_num [dyadicKernel_eq_sum_range, moment_zero]
  | succ q =>
      rw [dyadicKernel_eq_sum_range]
      have hdiv : (2 * (q + 1) + 1) / 2 + 1 = (q + 1) + 1 := by omega
      rw [hdiv, Finset.sum_range_succ]
      simp only [one_pow, mul_one]
      have hchoose : Nat.choose (2 * (q + 1) + 1) (2 * (q + 1)) =
          2 * (q + 1) + 1 := by
        rw [show 2 * (q + 1) + 1 = (2 * (q + 1)) + 1 by omega,
          Nat.choose_succ_self_right]
      rw [hchoose]
      let S : ℚ := ∑ k ∈ Finset.range (q + 1),
        (Nat.choose (2 * (q + 1) + 1) (2 * k) : ℚ) * moment k
      have hmoment : moment (q + 1) =
          S / (((2 * (q + 1) + 1 : ℕ) : ℚ) *
            ((2 : ℚ) ^ (2 * (q + 1)) - 1)) := by
        rw [moment_succ]
        let g : ℕ → ℚ := fun k =>
          (Nat.choose (2 * (q + 1) + 1) (2 * k) : ℚ) * moment k
        change (∑ k : Fin (q + 1), g k.val) / _ = S / _
        rw [Fin.sum_univ_eq_sum_range g (q + 1)]
      rw [hmoment]
      have hpow : (1 : ℚ) < (2 : ℚ) ^ (2 * (q + 1)) := by
        exact one_lt_pow₀ (by norm_num) (by omega)
      have hden :
          (((2 * (q + 1) + 1 : ℕ) : ℚ) *
            ((2 : ℚ) ^ (2 * (q + 1)) - 1)) ≠ 0 := by positivity
      have hpowden : (2 : ℚ) ^ (2 * (q + 1)) - 1 ≠ 0 :=
        ne_of_gt (sub_pos.mpr hpow)
      change S + ((2 * (q + 1) + 1 : ℕ) : ℚ) * (S / _) =
        ((2 * (q + 1) + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (2 * (q + 1)) * (S / _)
      field_simp [hden, hpowden]
      ring

/-- The kernel has the parity of its index: `dyadicKernel n (-x)` equals
`(-1) ^ n * dyadicKernel n x`, because every exponent `n - 2 k` occurring in
it has the parity of `n`. -/
lemma dyadicKernel_neg (n : ℕ) (x : ℚ) :
    dyadicKernel n (-x) = (-1 : ℚ) ^ n * dyadicKernel n x := by
  rw [dyadicKernel_eq_sum_range, dyadicKernel_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le_div : k ≤ n / 2 := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hk
  have htwok : 2 * k ≤ n := by
    have := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp hk_le_div
    omega
  have hparity : Even (n - 2 * k) ↔ Even n := by
    rw [Nat.even_sub htwok]
    simp
  have hsign : (-1 : ℚ) ^ (n - 2 * k) = (-1 : ℚ) ^ n :=
    neg_one_pow_congr hparity
  rw [show -x = (-1 : ℚ) * x by ring, mul_pow, hsign]
  ring

/-- At the origin only the constant term of an even-index kernel survives,
leaving `dyadicKernel (2 q) 0 = moment q`.  This uses the convention
`0 ^ 0 = 1` for the term `k = q`. -/
lemma dyadicKernel_even_zero (q : ℕ) :
    dyadicKernel (2 * q) 0 = moment q := by
  rw [dyadicKernel_eq_sum_range]
  have hdiv : (2 * q) / 2 + 1 = q + 1 := by omega
  rw [hdiv]
  calc
    _ = (Nat.choose (2 * q) (2 * q) : ℚ) * 0 ^ (2 * q - 2 * q) * moment q := by
      apply Finset.sum_eq_single q
      · intro k hk hne
        have hklt : k < q := by
          have : k < q + 1 := Finset.mem_range.mp hk
          omega
        have hpow : 2 * q - 2 * k ≠ 0 := by omega
        simp [hpow]
      · simp
    _ = _ := by simp

/-- Every exponent occurring in an odd-index kernel is positive, so
`dyadicKernel (2 q + 1) 0 = 0`. -/
lemma dyadicKernel_odd_zero (q : ℕ) :
    dyadicKernel (2 * q + 1) 0 = 0 := by
  rw [dyadicKernel_eq_sum_range]
  apply Finset.sum_eq_zero
  intro k hk
  have hk_le : k ≤ q := by
    have : k < (2 * q + 1) / 2 + 1 := Finset.mem_range.mp hk
    omega
  have hpow : 2 * q + 1 - 2 * k ≠ 0 := by omega
  simp [hpow]

/-- The `j = 1` case of `dyadicKernelPolynomial_hasseDeriv`: differentiating
the kernel polynomial lowers its index by one and multiplies by `n + 1`. -/
lemma dyadicKernelPolynomial_derivative_succ (n : ℕ) :
    (dyadicKernelPolynomial (n + 1)).derivative =
      Polynomial.C ((n + 1 : ℕ) : ℚ) * dyadicKernelPolynomial n := by
  simpa using dyadicKernelPolynomial_hasseDeriv (n + 1) 1 (by omega)

/-- The affine substitution `2 X + 1`, the right branch of the refinement. -/
private noncomputable def dyadicAffinePlus : Polynomial ℚ :=
  Polynomial.C 2 * Polynomial.X + Polynomial.C 1

/-- The affine substitution `2 X - 1`, the left branch of the refinement. -/
private noncomputable def dyadicAffineMinus : Polynomial ℚ :=
  Polynomial.C 2 * Polynomial.X - Polynomial.C 1

/-- **Kernel refinement law, polynomial form.**  Composing the index-`n + 1`
kernel polynomial with `2 X + 1` and with `2 X - 1` and subtracting gives
`(n + 1) * 2 ^ (n + 1)` times the index-`n` kernel polynomial.  The induction
compares derivatives, then pins the remaining constant using the parity and
endpoint evaluations above.  `dyadicKernel_has_refinement` evaluates this
identity at a point. -/
lemma dyadicKernelPolynomial_refinement (n : ℕ) :
    (dyadicKernelPolynomial (n + 1)).comp dyadicAffinePlus -
        (dyadicKernelPolynomial (n + 1)).comp dyadicAffineMinus =
      Polynomial.C (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1)) *
        dyadicKernelPolynomial n := by
  induction n with
  | zero =>
      norm_num [dyadicKernelPolynomial, dyadicAffinePlus, dyadicAffineMinus]
      exact (Polynomial.C_ofNat 2).symm
  | succ n ih =>
      let defect :=
        (dyadicKernelPolynomial (n + 2)).comp dyadicAffinePlus -
          (dyadicKernelPolynomial (n + 2)).comp dyadicAffineMinus -
            Polynomial.C ((((n + 1) + 1 : ℕ) : ℚ) *
              (2 : ℚ) ^ ((n + 1) + 1)) * dyadicKernelPolynomial (n + 1)
      have hderiv : defect.derivative = 0 := by
        have hplus : dyadicAffinePlus.derivative = Polynomial.C 2 := by
          simp [dyadicAffinePlus]
        have hminus : dyadicAffineMinus.derivative = Polynomial.C 2 := by
          simp [dyadicAffineMinus]
        rw [show defect =
          (dyadicKernelPolynomial (n + 2)).comp dyadicAffinePlus -
            (dyadicKernelPolynomial (n + 2)).comp dyadicAffineMinus -
              Polynomial.C ((((n + 1) + 1 : ℕ) : ℚ) *
                (2 : ℚ) ^ ((n + 1) + 1)) *
                  dyadicKernelPolynomial (n + 1) by rfl]
        rw [Polynomial.derivative_sub, Polynomial.derivative_sub,
          Polynomial.derivative_comp, Polynomial.derivative_comp,
          hplus, hminus,
          dyadicKernelPolynomial_derivative_succ,
          Polynomial.mul_comp, Polynomial.mul_comp,
          Polynomial.C_comp, Polynomial.C_comp,
          Polynomial.derivative_C_mul,
          dyadicKernelPolynomial_derivative_succ]
        have hfactor :
            Polynomial.C (2 : ℚ) *
                (Polynomial.C (((n + 1) + 1 : ℕ) : ℚ) *
                  (dyadicKernelPolynomial (n + 1)).comp dyadicAffinePlus) -
              Polynomial.C (2 : ℚ) *
                (Polynomial.C (((n + 1) + 1 : ℕ) : ℚ) *
                  (dyadicKernelPolynomial (n + 1)).comp dyadicAffineMinus) =
            Polynomial.C (2 : ℚ) * Polynomial.C (((n + 1) + 1 : ℕ) : ℚ) *
              ((dyadicKernelPolynomial (n + 1)).comp dyadicAffinePlus -
                (dyadicKernelPolynomial (n + 1)).comp dyadicAffineMinus) := by ring
        rw [hfactor]
        rw [ih]
        have hcoeff :
            (2 : ℚ) * (((n + 1) + 1 : ℕ) : ℚ) *
                ((((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1))) =
              (((((n + 1) + 1 : ℕ) : ℚ) * (2 : ℚ) ^ ((n + 1) + 1))) *
                ((n + 1 : ℕ) : ℚ) := by
          push_cast
          rw [pow_succ]
          ring
        have hcoeffPoly :
            Polynomial.C (2 : ℚ) *
                Polynomial.C (((n + 1) + 1 : ℕ) : ℚ) *
                Polynomial.C (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1)) =
              Polynomial.C ((((n + 1) + 1 : ℕ) : ℚ) *
                  (2 : ℚ) ^ ((n + 1) + 1)) *
                Polynomial.C ((n + 1 : ℕ) : ℚ) := by
          calc
            _ = Polynomial.C
                ((2 : ℚ) * (((n + 1) + 1 : ℕ) : ℚ) *
                  (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1))) := by
                    repeat rw [← Polynomial.C_mul]
            _ = Polynomial.C
                (((((n + 1) + 1 : ℕ) : ℚ) * (2 : ℚ) ^ ((n + 1) + 1)) *
                  ((n + 1 : ℕ) : ℚ)) := by rw [hcoeff]
            _ = _ := by rw [Polynomial.C_mul]
        calc
          _ = (Polynomial.C (2 : ℚ) *
                  Polynomial.C (((n + 1) + 1 : ℕ) : ℚ) *
                  Polynomial.C (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1))) *
                dyadicKernelPolynomial n -
              (Polynomial.C ((((n + 1) + 1 : ℕ) : ℚ) *
                  (2 : ℚ) ^ ((n + 1) + 1)) *
                Polynomial.C ((n + 1 : ℕ) : ℚ)) *
                dyadicKernelPolynomial n := by ring
          _ = 0 := by rw [hcoeffPoly]; ring
      have hconst := Polynomial.eq_C_of_derivative_eq_zero hderiv
      have heval : defect.eval 0 = 0 := by
        have hplus0 : dyadicAffinePlus.eval 0 = 1 := by
          norm_num [dyadicAffinePlus]
        have hminus0 : dyadicAffineMinus.eval 0 = -1 := by
          norm_num [dyadicAffineMinus]
        simp only [defect, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_comp, hplus0, hminus0,
          dyadicKernelPolynomial_eval]
        obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' n
        · subst n
          rw [dyadicKernel_neg, dyadicKernel_odd_zero]
          have heven : (-1 : ℚ) ^ (2 * q + 2) = 1 := by
            rw [show 2 * q + 2 = 2 * (q + 1) by omega, pow_mul]
            norm_num
          rw [heven]
          ring
        · subst n
          rw [dyadicKernel_neg]
          have hoddIndex : 2 * q + 1 + 2 = 2 * (q + 1) + 1 := by omega
          have hevenIndex : 2 * q + 1 + 1 = 2 * (q + 1) := by omega
          rw [hoddIndex, hevenIndex,
            dyadicKernel_odd_one (q + 1), dyadicKernel_even_zero (q + 1)]
          have hodd : (-1 : ℚ) ^ (2 * (q + 1) + 1) = -1 := by
            rw [pow_succ, pow_mul]
            norm_num
          rw [hodd]
          push_cast
          rw [pow_succ]
          ring
      have hzero : defect = 0 := by
        calc
          defect = Polynomial.C (defect.coeff 0) := hconst
          _ = Polynomial.C (defect.eval 0) := by rw [Polynomial.coeff_zero_eq_eval_zero]
          _ = 0 := by rw [heval, Polynomial.C_0]
      exact sub_eq_zero.mp hzero

/-- The normalization absorbs exactly the constant produced by the kernel
refinement law: `dyadicScale (n + 1) * (n + 1) * 2 ^ (n + 1) = dyadicScale n`.
This cancellation is what makes `fabiusDyadic` invariant under refining the
dyadic grid. -/
lemma dyadicScale_succ_mul (n : ℕ) :
    dyadicScale (n + 1) * ((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1) =
      dyadicScale n := by
  have hchoose : (n + 2).choose 2 = (n + 1).choose 2 + (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega,
      show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
    simp [Nat.add_comm]
  rw [dyadicScale, dyadicScale, show n + 1 + 1 = n + 2 by omega, hchoose,
    Nat.factorial_succ]
  push_cast
  have hexp :
      -((Nat.choose (n + 1) 2 : ℤ) + ((n : ℤ) + 1)) =
        -(Nat.choose (n + 1) 2 : ℤ) - ((n : ℤ) + 1) := by ring
  rw [hexp, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
  simp only [div_eq_mul_inv]
  rw [mul_inv]
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hp : (2 : ℚ) ^ (n + 1) ≠ 0 := by positivity
  have hz : (2 : ℚ) ^ ((n : ℤ) + 1) = (2 : ℚ) ^ (n + 1) := by
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega, zpow_natCast]
  rw [hz]
  calc
    _ = (2 : ℚ) ^ (-(Nat.choose (n + 1) 2 : ℤ)) *
          (n.factorial : ℚ)⁻¹ *
          (((n : ℚ) + 1)⁻¹ * ((n : ℚ) + 1)) *
          (((2 : ℚ) ^ (n + 1))⁻¹ * (2 : ℚ) ^ (n + 1)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hn, inv_mul_cancel₀ hp]; ring

/-- Regrouping of a single Taylor coefficient, for `j ≤ n`:
`dyadicScale n * Nat.choose n j * (2 r) ^ j` equals
`2 ^ Nat.choose (j + 1) 2 * (r / 2 ^ n) ^ j / j ! * dyadicScale (n - j)`.
This converts the block expansion into the shape evaluated by
`fabiusTaylorHorner`; the exponent bookkeeping is `choose_add_succ_two`. -/
lemma dyadicScale_choose_taylor (n j : ℕ) (hj : j ≤ n) (r : ℚ) :
    dyadicScale n * (Nat.choose n j : ℚ) * ((2 : ℚ) * r) ^ j =
      (2 : ℚ) ^ (j + 1).choose 2 *
        (r / (2 : ℚ) ^ n) ^ j / j.factorial * dyadicScale (n - j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_sub_cancel_left]
  simp only [dyadicScale]
  rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, div_pow]
  have hfac := Nat.choose_mul_factorial_mul_factorial (n := j + m) (k := j) hj
  have hchoose := choose_add_succ_two m j
  have hpow0 : (2 : ℚ) ^ (j + m + 1).choose 2 ≠ 0 := by positivity
  have hpowm : (2 : ℚ) ^ (m + 1).choose 2 ≠ 0 := by positivity
  have hpown : (2 : ℚ) ^ (j + m) ≠ 0 := by positivity
  field_simp [hpow0, hpowm, hpown]
  have hfacNat : Nat.choose (j + m) j * j.factorial * m.factorial =
      (j + m).factorial := by simpa using hfac
  have hfacQ : (Nat.choose (j + m) j : ℚ) * j.factorial * m.factorial =
      ((j + m).factorial : ℚ) := by exact_mod_cast hfacNat
  have hchoose' : Nat.choose (j + m + 1) 2 =
      Nat.choose (m + 1) 2 + m * j + Nat.choose (j + 1) 2 := by
    simpa [add_comm] using hchoose
  have hjprod : j * j + j = 2 * Nat.choose (j + 1) 2 := by
    calc
      j * j + j = j * (j + 1) := by ring
      _ = _ := (two_mul_choose_succ_two j).symm
  have hexponent :
      j + (j + m) * j + Nat.choose (m + 1) 2 =
        Nat.choose (j + m + 1) 2 + Nat.choose (j + 1) 2 := by
    rw [show (j + m) * j = j * j + m * j by ring, hchoose']
    omega
  have hpowers :
      (2 : ℚ) ^ j * ((2 : ℚ) ^ (j + m)) ^ j *
          (2 : ℚ) ^ (m + 1).choose 2 =
        (2 : ℚ) ^ (j + m + 1).choose 2 *
          (2 : ℚ) ^ (j + 1).choose 2 := by
    rw [← pow_mul]
    calc
      (2 : ℚ) ^ j * 2 ^ ((j + m) * j) * 2 ^ (m + 1).choose 2 =
          2 ^ (j + (j + m) * j + (m + 1).choose 2) := by
            rw [← pow_add, ← pow_add]
      _ = 2 ^ ((j + m + 1).choose 2 + (j + 1).choose 2) := by rw [hexponent]
      _ = _ := by rw [pow_add]
  rw [mul_pow]
  calc
    _ = ((Nat.choose (j + m) j : ℚ) * j.factorial * m.factorial) *
          ((2 : ℚ) ^ j * ((2 : ℚ) ^ (j + m)) ^ j *
            (2 : ℚ) ^ (m + 1).choose 2) * r ^ j := by ring
    _ = ((j + m).factorial : ℚ) *
          ((2 : ℚ) ^ (j + m + 1).choose 2 *
            (2 : ℚ) ^ (j + 1).choose 2) * r ^ j := by rw [hfacQ, hpowers]
    _ = _ := by ring

/-- A complete Thue--Morse block annihilates a kernel of lower index: for
`n < b` the signed sum of `dyadicKernel n (x - 2 h)` over `h < 2 ^ b` vanishes,
for every `x`.  Each monomial has degree at most `n < b`, so
`thueMorse_affine_power_sum_eq_zero` applies term by term.  This is what
truncates the expansion in `dyadicBlock_expand_truncated`. -/
lemma thueMorse_kernel_block_eq_zero (n b : ℕ) (hn : n < b) (x : ℚ) :
    (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
      dyadicKernel n (x - 2 * h.val)) = 0 := by
  simp_rw [dyadicKernel, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  have hdegree : n - 2 * k.val < b := (Nat.sub_le n _).trans_lt hn
  have hzero := thueMorse_affine_power_sum_eq_zero b (n - 2 * k.val)
    hdegree x (-2)
  have heq :
      (∑ h : Fin (2 ^ b),
        (thueMorseSign h.val : ℚ) *
          ((Nat.choose n (2 * k.val) : ℚ) *
            (x - 2 * (h.val : ℚ)) ^ (n - 2 * k.val) * moment k.val)) =
        ((Nat.choose n (2 * k.val) : ℚ) * moment k.val) *
          ∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            (x + (-2) * (h.val : ℚ)) ^ (n - 2 * k.val) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  rw [heq, hzero, mul_zero]

/-- Taylor-expands the scaled signed block sum in the displacement `2 r`:
adding `2 r` to every kernel argument spreads the sum over the `n + 1` terms
of `dyadicKernel_taylor`, each carrying its own signed block sum at kernel
index `n - j`. -/
lemma dyadicBlock_expand (n b : ℕ) (r : ℚ) :
    dyadicScale n *
        (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
          dyadicKernel n
            (((2 : ℚ) * 2 ^ b - 2 * h.val - 1) + 2 * r)) =
      ∑ j ∈ Finset.range (n + 1),
        dyadicScale n * (Nat.choose n j : ℚ) * ((2 : ℚ) * r) ^ j *
          (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) := by
  simp_rw [dyadicKernel_taylor]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro h hh
  ring

/-- The expansion of `dyadicBlock_expand`, truncated to `j ≤ n - b` under the
hypothesis `b ≤ n`.  The discarded terms vanish because their kernel index
`n - j` drops below `b`, where `thueMorse_kernel_block_eq_zero` applies. -/
lemma dyadicBlock_expand_truncated (n b : ℕ) (hb : b ≤ n) (r : ℚ) :
    dyadicScale n *
        (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
          dyadicKernel n
            (((2 : ℚ) * 2 ^ b - 2 * h.val - 1) + 2 * r)) =
      ∑ j ∈ Finset.range (n - b + 1),
        dyadicScale n * (Nat.choose n j : ℚ) * ((2 : ℚ) * r) ^ j *
          (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) := by
  rw [dyadicBlock_expand]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (Nat.sub_le n b) 1))
  intro j hj hnot
  have hjle : j ≤ n := by simpa using Finset.mem_range.mp hj
  have hdlt : n - b < j := by
    simpa only [Finset.mem_range, Nat.not_lt, Nat.add_one_le_iff] using hnot
  have hdegree : n - j < b := by omega
  have hzero := thueMorse_kernel_block_eq_zero (n - j) b hdegree
    ((2 : ℚ) * 2 ^ b - 1)
  have hzero' :
      (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
        dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) = 0 := by
    convert hzero using 1
    all_goals ring_nf
  rw [hzero', mul_zero]

/-- The kernel refinement law as a `Prop`: for all `n` and all rational `x`,
`dyadicKernel (n + 1) (2 x + 1) - dyadicKernel (n + 1) (2 x - 1)` equals
`(n + 1) * 2 ^ (n + 1) * dyadicKernel n x`.  Packaging it this way lets the
consequences below be stated as hypothetical implications; it is discharged
once, by `dyadicKernel_has_refinement`. -/
def DyadicKernelHasRefinement : Prop :=
  ∀ n : ℕ, ∀ x : ℚ,
    dyadicKernel (n + 1) (2 * x + 1) -
        dyadicKernel (n + 1) (2 * x - 1) =
      ((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1) * dyadicKernel n x

/-- The refinement law holds, by evaluating the polynomial identity
`dyadicKernelPolynomial_refinement` at each rational point. -/
theorem dyadicKernel_has_refinement : DyadicKernelHasRefinement := by
  intro n x
  have h := congrArg (Polynomial.eval x) (dyadicKernelPolynomial_refinement n)
  simpa [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, dyadicAffinePlus, dyadicAffineMinus,
    dyadicKernelPolynomial_eval] using h

/-- Unfolds equation (32) into the normalization `dyadicScale n` times the
signed kernel sum, the shape every proof in this file works with.  It holds by
`rfl`, so rewriting with it in either direction is free. -/
lemma fabiusDyadic_eq_scale_sum (n a : ℕ) :
    fabiusDyadic n a = dyadicScale n *
      ∑ h : Fin a, (thueMorseSign h.val : ℚ) *
        dyadicKernel n ((2 : ℚ) * a - 2 * h.val - 1) := by
  rfl

/-- **Thue--Morse block concatenation.**  Splitting an index as a multiple of
`2 ^ k` plus a residue below `2 ^ k` splits its Thue--Morse sign into the
product of the signs of the two parts, because the binary expansions of
`h * 2 ^ k` and of `r` occupy disjoint digit ranges.

This multiplicativity is what makes every dyadic Fabius numerator
quasi-periodic.  It is public because the uniform-spline and q-binomial layers
need it too; all three had previously proved it privately. -/
theorem thueMorseSign_block_concat
    (k h r : ℕ) (hr : r < 2 ^ k) :
    thueMorseSign (h * 2 ^ k + r) =
      thueMorseSign h * thueMorseSign r := by
  induction k generalizing h r with
  | zero =>
      have : r = 0 := by omega
      subst r
      norm_num [thueMorseSign, binaryWeight]
  | succ k ih =>
      rcases r.even_or_odd with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · have hr' : r < 2 ^ k := by
          rw [pow_succ] at hr
          omega
        rw [show r + r = 2 * r by omega]
        rw [show h * 2 ^ (k + 1) + 2 * r =
            2 * (h * 2 ^ k + r) by rw [pow_succ]; ring,
          thueMorseSign_two_mul, thueMorseSign_two_mul, ih h r hr']
      · have hr' : r < 2 ^ k := by
          rw [pow_succ] at hr
          omega
        rw [show h * 2 ^ (k + 1) + (2 * r + 1) =
            2 * (h * 2 ^ k + r) + 1 by rw [pow_succ]; ring,
          thueMorseSign_two_mul_add_one,
          thueMorseSign_two_mul_add_one, ih h r hr']
        ring

/-- **Block decomposition of a range sum.**  A sum over `Finset.range (m * p)`
is the sum of `m` consecutive blocks of length `p`.  Stated over an arbitrary
`AddCommMonoid`, since the corpus applies it over the rationals, over the
reals, and over formal power series.

Mathlib has no equivalent: it has `Finset.sum_range_add` for a two-part split
and `Finset.sum_range_add_sum_Ico` for a range/interval split, but nothing
that splits `range (m * p)` into `m` blocks for symbolic `m` and `p`.  A
tree-wide search of Mathlib for `range (a * b)` with two symbolic variables
finds no occurrence at all, and `Combinatorics.SimpleGraph.Extremal.Turan`
does this decomposition by hand.  So do not replace this by an import. -/
theorem sum_range_block_decomposition
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (m p : ℕ) :
    (∑ j ∈ Finset.range (m * p), f j) =
      ∑ h ∈ Finset.range m, ∑ r ∈ Finset.range p, f (h * p + r) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih,
        Finset.sum_range_succ]

/-- **Block decomposition with a partial final block.**  The variant of
`sum_range_block_decomposition` for a range whose length `m * p + r` need not
be a multiple of the block length `p`. -/
theorem sum_range_block_decomposition_with_remainder
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (m p r : ℕ) :
    (∑ j ∈ Finset.range (m * p + r), f j) =
      (∑ h ∈ Finset.range m,
        ∑ j ∈ Finset.range p, f (h * p + j)) +
      ∑ j ∈ Finset.range r, f (m * p + j) := by
  rw [Finset.sum_range_add, sum_range_block_decomposition]

/-- Equation (32) transforms by the Thue--Morse sign when its numerator is
translated by a complete length-`2^(n+1)` block. -/
theorem fabiusDyadic_block_translate (n block residue : ℕ)
    (hresidue : residue < 2 ^ (n + 1)) :
    fabiusDyadic n (block * 2 ^ (n + 1) + residue) =
      (thueMorseSign block : ℚ) * fabiusDyadic n residue := by
  rw [fabiusDyadic_eq_scale_sum, fabiusDyadic_eq_scale_sum]
  let scale : ℚ := dyadicScale n
  let period : ℕ := 2 ^ (n + 1)
  let a : ℕ := block * period + residue
  let f : ℕ → ℚ := fun h =>
    (thueMorseSign h : ℚ) *
      dyadicKernel n ((2 : ℚ) * a - 2 * h - 1)
  change scale * (∑ h : Fin a, f h.val) =
    (thueMorseSign block : ℚ) *
      (scale * ∑ h : Fin residue,
        (thueMorseSign h.val : ℚ) *
          dyadicKernel n ((2 : ℚ) * residue - 2 * h.val - 1))
  rw [Fin.sum_univ_eq_sum_range f a,
    sum_range_block_decomposition_with_remainder f block period residue]
  have hfull :
      (∑ q ∈ Finset.range block,
        ∑ j ∈ Finset.range period, f (q * period + j)) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    have hblockzero := thueMorse_kernel_block_eq_zero n (n + 1)
      (Nat.lt_succ_self n)
      ((2 : ℚ) * a - 2 * (q * period : ℕ) - 1)
    calc
      (∑ j ∈ Finset.range period, f (q * period + j)) =
          (thueMorseSign q : ℚ) *
            ∑ j ∈ Finset.range period,
              (thueMorseSign j : ℚ) *
                dyadicKernel n
                  ((2 : ℚ) * a - 2 * (q * period : ℕ) - 1 - 2 * j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjlt : j < period := Finset.mem_range.mp hj
        dsimp only [f]
        rw [thueMorseSign_block_concat (n + 1) q j
          (by simpa [period] using hjlt)]
        push_cast
        ring_nf
      _ = 0 := by
        rw [← Fin.sum_univ_eq_sum_range
          (fun j => (thueMorseSign j : ℚ) *
            dyadicKernel n
              ((2 : ℚ) * a - 2 * (q * period : ℕ) - 1 - 2 * j)) period,
          hblockzero, mul_zero]
  rw [hfull, zero_add]
  rw [Fin.sum_univ_eq_sum_range
    (fun h => (thueMorseSign h : ℚ) *
      dyadicKernel n ((2 : ℚ) * residue - 2 * h - 1)) residue]
  calc
    scale * ∑ j ∈ Finset.range residue, f (block * period + j) =
        scale * ((thueMorseSign block : ℚ) *
          ∑ j ∈ Finset.range residue,
            (thueMorseSign j : ℚ) *
              dyadicKernel n ((2 : ℚ) * residue - 2 * j - 1)) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < period := (Finset.mem_range.mp hj).trans hresidue
      dsimp only [f, a]
      rw [thueMorseSign_block_concat (n + 1) block j
        (by simpa [period] using hjlt)]
      push_cast
      dsimp only [period]
      ring_nf
    _ = _ := by ring

/-- The closed dyadic formula vanishes at the right endpoint `2`. -/
@[simp]
theorem fabiusDyadic_two_pow_succ (n : ℕ) :
    fabiusDyadic n (2 ^ (n + 1)) = 0 := by
  simpa [fabiusDyadic_arg_zero] using
    fabiusDyadic_block_translate n 1 0 (by positivity)

/-- The block-translation law also holds at the right endpoint of a block.
Both sides then vanish, so callers may use the natural closed-block bound. -/
theorem fabiusDyadic_block_translate_le (n block residue : ℕ)
    (hresidue : residue ≤ 2 ^ (n + 1)) :
    fabiusDyadic n (block * 2 ^ (n + 1) + residue) =
      (thueMorseSign block : ℚ) * fabiusDyadic n residue := by
  rcases hresidue.eq_or_lt with rfl | hresidue
  · calc
      fabiusDyadic n (block * 2 ^ (n + 1) + 2 ^ (n + 1)) =
          fabiusDyadic n ((block + 1) * 2 ^ (n + 1) + 0) := by
        congr 1
        ring
      _ = (thueMorseSign (block + 1) : ℚ) * fabiusDyadic n 0 :=
        fabiusDyadic_block_translate n (block + 1) 0 (by positivity)
      _ = 0 := by rw [fabiusDyadic_arg_zero, mul_zero]
      _ = (thueMorseSign block : ℚ) * fabiusDyadic n (2 ^ (n + 1)) := by
        rw [fabiusDyadic_two_pow_succ, mul_zero]
  · exact fabiusDyadic_block_translate n block residue hresidue

/-- **Canonical block normal form.**  Dividing an arbitrary numerator `a`
by the natural period `2 ^ (n + 1)` separates its closed-form dyadic value
into the Thue--Morse sign of the block quotient and the value at the canonical
remainder:

`fabiusDyadic n a = thueMorseSign (a / 2 ^ (n + 1)) *
  fabiusDyadic n (a % 2 ^ (n + 1))`.

This includes level `n = 0`, the numerator `a = 0`, and exact block multiples;
in the latter case the remainder is zero and both sides vanish. -/
theorem fabiusDyadic_eq_block_sign_mul_mod (n a : ℕ) :
    fabiusDyadic n a =
      (thueMorseSign (a / 2 ^ (n + 1)) : ℚ) *
        fabiusDyadic n (a % 2 ^ (n + 1)) := by
  have hperiod : 0 < 2 ^ (n + 1) := by positivity
  have hdecomp :
      a / 2 ^ (n + 1) * 2 ^ (n + 1) + a % 2 ^ (n + 1) = a := by
    calc
      a / 2 ^ (n + 1) * 2 ^ (n + 1) + a % 2 ^ (n + 1) =
          2 ^ (n + 1) * (a / 2 ^ (n + 1)) + a % 2 ^ (n + 1) := by
        rw [Nat.mul_comm]
      _ = a := Nat.div_add_mod a (2 ^ (n + 1))
  simpa only [hdecomp] using
    fabiusDyadic_block_translate n (a / 2 ^ (n + 1))
      (a % 2 ^ (n + 1)) (Nat.mod_lt a hperiod)

/-- Assuming the kernel refinement law, equation (32) is consistent under
refining the dyadic grid: `fabiusDyadic (n + 1) (2 a) = fabiusDyadic n a`, so
the value depends only on the rational `a / 2 ^ n`.  Callers supply
`dyadicKernel_has_refinement` for `hk`. -/
lemma fabiusDyadic_refine_of_kernel (hk : DyadicKernelHasRefinement)
    (n a : ℕ) :
    fabiusDyadic (n + 1) (2 * a) = fabiusDyadic n a := by
  rw [fabiusDyadic_eq_scale_sum, fabiusDyadic_eq_scale_sum]
  push_cast
  let f : ℕ → ℚ := fun h =>
    dyadicKernel (n + 1) ((2 : ℚ) * (2 * a) - 2 * h - 1)
  change dyadicScale (n + 1) *
      (∑ h : Fin (2 * a), (thueMorseSign h.val : ℚ) * f h.val) =
    dyadicScale n *
      ∑ h : Fin a, (thueMorseSign h.val : ℚ) *
        dyadicKernel n ((2 : ℚ) * a - 2 * h.val - 1)
  rw [thueMorse_sum_two_mul a f]
  have hterms :
      (∑ j : Fin a, (thueMorseSign j.val : ℚ) *
          (f (2 * j.val) - f (2 * j.val + 1))) =
        ((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1) *
          ∑ j : Fin a, (thueMorseSign j.val : ℚ) *
            dyadicKernel n ((2 : ℚ) * a - 2 * j.val - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hrefine := hk n ((2 : ℚ) * a - 2 * j.val - 1)
    simp only [f]
    push_cast
    have hdiff :
        dyadicKernel (n + 1)
            (2 * (2 * (a : ℚ)) - 2 * (2 * (j.val : ℚ)) - 1) -
          dyadicKernel (n + 1)
            (2 * (2 * (a : ℚ)) - 2 * (2 * (j.val : ℚ) + 1) - 1) =
          ((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1) *
            dyadicKernel n (2 * (a : ℚ) - 2 * (j.val : ℚ) - 1) := by
      convert hrefine using 1; ring_nf
    rw [hdiff]
    push_cast
    ring
  rw [hterms]
  rw [← mul_assoc, ← mul_assoc, dyadicScale_succ_mul]

/-- Iterating `fabiusDyadic_refine_of_kernel` `b` times: refining the grid by
a factor `2 ^ b` leaves the closed-form value unchanged. -/
lemma fabiusDyadic_refine_pow_of_kernel (hk : DyadicKernelHasRefinement)
    (m b a : ℕ) :
    fabiusDyadic (m + b) (2 ^ b * a) = fabiusDyadic m a := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [show m + (b + 1) = (m + b) + 1 by omega,
        pow_succ', mul_assoc, fabiusDyadic_refine_of_kernel hk, ih]

/-- The case `a = 1` of `fabiusDyadic_refine_pow_of_kernel`: every grid
representation of `2 ^ (-m)` gives the tabulated value
`fabiusAtInverseTwoPow m`. -/
lemma fabiusDyadic_pow_two_eq_inverse_of_kernel (hk : DyadicKernelHasRefinement)
    (m b : ℕ) :
    fabiusDyadic (m + b) (2 ^ b) = fabiusAtInverseTwoPow m := by
  simpa [fabiusAtInverseTwoPow] using
    fabiusDyadic_refine_pow_of_kernel hk m b 1

/-- Identifies the constant term of the block expansion: the scaled signed
kernel sum over a complete block `h < 2 ^ b`, with kernel arguments
`2 * 2 ^ b - 2 h - 1`, is `fabiusAtInverseTwoPow m`.  Same content as
`fabiusDyadic_pow_two_eq_inverse_of_kernel`, written in the summed form that
`dyadicBlock_eq_taylor_sum` consumes. -/
lemma dyadic_block_base_eq_inverse_of_kernel (hk : DyadicKernelHasRefinement)
    (m b : ℕ) :
    dyadicScale (m + b) *
        (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
          dyadicKernel (m + b) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) =
      fabiusAtInverseTwoPow m := by
  calc
    _ = fabiusDyadic (m + b) (2 ^ b) := by
      rw [fabiusDyadic_eq_scale_sum]
      push_cast
      rfl
    _ = _ := fabiusDyadic_pow_two_eq_inverse_of_kernel hk m b

/-- **The block Taylor identity.**  For `b ≤ n` and any rational `r`, the
scaled signed kernel sum over the block `h < 2 ^ b`, with its argument
displaced by `2 r`, equals the finite sum over `j ≤ n - b` of
`2 ^ Nat.choose (j + 1) 2 * fabiusAtInverseTwoPow (n - b - j) *
(r / 2 ^ n) ^ j / j !`.  Every coefficient is a tabulated inverse-power value,
which is what makes the Horner evaluator exact.  `GlobalDyadic` and
`DyadicAnalytic` use it as well as the correctness proof below. -/
lemma dyadicBlock_eq_taylor_sum (n b : ℕ) (hb : b ≤ n) (r : ℚ) :
    dyadicScale n *
        (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
          dyadicKernel n
            (((2 : ℚ) * 2 ^ b - 2 * h.val - 1) + 2 * r)) =
      ∑ j ∈ Finset.range (n - b + 1),
        (2 : ℚ) ^ (j + 1).choose 2 * fabiusAtInverseTwoPow (n - b - j) *
          (r / (2 : ℚ) ^ n) ^ j / j.factorial := by
  rw [dyadicBlock_expand_truncated n b hb r]
  apply Finset.sum_congr rfl
  intro j hj
  have hjleD : j ≤ n - b := by simpa using Finset.mem_range.mp hj
  have hjle : j ≤ n := hjleD.trans (Nat.sub_le n b)
  have hindex : n - j = (n - b - j) + b := by omega
  have hbase := dyadic_block_base_eq_inverse_of_kernel
    dyadicKernel_has_refinement (n - b - j) b
  have hbase' :
      dyadicScale (n - j) *
          (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) =
        fabiusAtInverseTwoPow (n - b - j) := by
    simpa [hindex] using hbase
  have hscale := dyadicScale_choose_taylor n j hjle r
  calc
    dyadicScale n * (Nat.choose n j : ℚ) * ((2 : ℚ) * r) ^ j *
          (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) =
        (dyadicScale n * (Nat.choose n j : ℚ) * ((2 : ℚ) * r) ^ j) *
          (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) := by ring
    _ = ((2 : ℚ) ^ (j + 1).choose 2 *
          (r / (2 : ℚ) ^ n) ^ j / j.factorial * dyadicScale (n - j)) *
          (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1)) := by
      rw [hscale]
    _ = ((2 : ℚ) ^ (j + 1).choose 2 *
          (r / (2 : ℚ) ^ n) ^ j / j.factorial) *
        (dyadicScale (n - j) *
          (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
            dyadicKernel (n - j) ((2 : ℚ) * 2 ^ b - 2 * h.val - 1))) := by ring
    _ = _ := by rw [hbase']; ring

/-- The precomputed table contains the exact values `F(2⁻ᵏ)`. -/
theorem fabiusInversePowTwoTable_get (maxExponent k : ℕ) (hk : k ≤ maxExponent) :
    (fabiusInversePowTwoTable maxExponent)[k]? = some (fabiusAtInverseTwoPow k) := by
  induction maxExponent generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      simp [fabiusInversePowTwoTable,
        fabiusAtInverseTwoPow_eq_halfMoment, halfMomentFabiusValue]
  | succ n ih =>
      rw [fabiusInversePowTwoTable, Array.getElem?_push,
        fabiusInversePowTwoTable_size]
      by_cases hlast : k = n + 1
      · subst k
        simp only [ite_true]
        congr 1
        rw [fabiusAtInverseTwoPow_eq_halfMoment,
          halfMomentFabiusValue_succ]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih j.val (by omega)]
        simp [fabiusAtInverseTwoPow_eq_halfMoment]
      · rw [if_neg hlast]
        exact ih k (by omega)

/-- The Horner routine evaluates the Taylor polynomial in Proposition 10. -/
theorem fabiusTaylorHorner_eq_sum (maxExponent order : ℕ)
    (horder : order ≤ maxExponent) (offset : ℚ) :
    fabiusTaylorHorner (fabiusInversePowTwoTable maxExponent) order offset =
      ∑ k ∈ range (order + 1),
        (2 : ℚ) ^ (k + 1).choose 2 * fabiusAtInverseTwoPow (order - k) *
          offset ^ k / k.factorial := by
  have hzero : fabiusInversePowTwoTableValue
      (fabiusInversePowTwoTable maxExponent) 0 = 1 := by
    rw [fabiusInversePowTwoTableValue,
      fabiusInversePowTwoTable_get maxExponent 0 (Nat.zero_le _)]
    simp [fabiusAtInverseTwoPow_eq_halfMoment, halfMomentFabiusValue]
  change fabiusTaylorHorner.go (fabiusInversePowTwoTable maxExponent)
      order offset order = _
  have hgo := fabiusTaylorHorner_go_eq_sum
    (fabiusInversePowTwoTable maxExponent) hzero offset order 0
  simp only [Nat.zero_add] at hgo
  rw [hgo]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ order := by simpa using hk
  have hlookup := fabiusInversePowTwoTable_get maxExponent (order - k)
    (le_trans (Nat.sub_le order k) horder)
  rw [fabiusInversePowTwoTableValue, hlookup]
  norm_num

/-- Splitting at a binary leading digit cancels the entire remainder block
against the value at that remainder. -/
lemma fabiusDyadic_add_remainder_eq_block (n b r : ℕ) (hr : r ≤ 2 ^ b) :
    fabiusDyadic n (2 ^ b + r) + fabiusDyadic n r =
      dyadicScale n *
        ∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
          dyadicKernel n ((2 : ℚ) * (2 ^ b + r) - 2 * h.val - 1) := by
  rw [fabiusDyadic_eq_scale_sum, fabiusDyadic_eq_scale_sum]
  push_cast
  rw [thueMorse_sum_split b r hr
    (fun h => dyadicKernel n ((2 : ℚ) * (2 ^ b + r) - 2 * h - 1))]
  have hshift :
      (∑ j : Fin r, (thueMorseSign j.val : ℚ) *
          dyadicKernel n
            ((2 : ℚ) * (2 ^ b + r) - 2 * (2 ^ b + j.val) - 1)) =
        ∑ j : Fin r, (thueMorseSign j.val : ℚ) *
          dyadicKernel n ((2 : ℚ) * r - 2 * j.val - 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    congr 2
    ring
  push_cast
  rw [hshift]
  ring

/-- Data attached to the leading binary bit of `a`: with `b = Nat.log2 a` and
`r = a - 2 ^ b` one has `b ≤ n`, `r < 2 ^ b`, and `a = 2 ^ b + r`.  These are
exactly the side conditions each step of the bit recursion needs; both `0 < a`
and `a ≤ 2 ^ n` are used. -/
lemma leading_bit_data (n a : ℕ) (ha0 : 0 < a) (ha : a ≤ 2 ^ n) :
    let b := Nat.log2 a
    let r := a - 2 ^ b
    b ≤ n ∧ r < 2 ^ b ∧ a = 2 ^ b + r := by
  dsimp
  have hane : a ≠ 0 := Nat.ne_of_gt ha0
  have hpow_le : 2 ^ Nat.log2 a ≤ a := Nat.log2_self_le hane
  have ha_lt_next : a < 2 ^ (Nat.log2 a + 1) := Nat.lt_log2_self
  have htwo_pow_lt : 2 ^ n < 2 ^ (n + 1) := by
    exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self n)
  have hlog_lt : Nat.log2 a < n + 1 :=
    (Nat.log2_lt hane).2 (ha.trans_lt htwo_pow_lt)
  have hb_le : Nat.log2 a ≤ n := by omega
  have hr_lt : a - 2 ^ Nat.log2 a < 2 ^ Nat.log2 a := by
    rw [pow_succ] at ha_lt_next
    omega
  exact ⟨hb_le, hr_lt, (Nat.add_sub_of_le hpow_le).symm⟩

/-- The one remaining polynomial identity after all bit-manipulation and
recursive cancellation have been discharged. -/
def FabiusDyadicHasBlockTaylor (values : Array ℚ) (n : ℕ) : Prop :=
  ∀ b r : ℕ, b ≤ n → r < 2 ^ b →
    dyadicScale n *
        (∑ h : Fin (2 ^ b), (thueMorseSign h.val : ℚ) *
          dyadicKernel n ((2 : ℚ) * (2 ^ b + r) - 2 * h.val - 1)) =
      fabiusTaylorHorner values (n - b) ((r : ℚ) / (2 : ℚ) ^ n)

/-- The block Taylor identity for a table of values implies the single-step
bit recurrence for that table: splitting `a` at its leading bit, cancelling the
remainder block by `fabiusDyadic_add_remainder_eq_block`, and rewriting the
block by `hblock` gives exactly the recurrence. -/
theorem blockTaylor_implies_bitRecurrence (values : Array ℚ) (n : ℕ)
    (hblock : FabiusDyadicHasBlockTaylor values n) :
    FabiusDyadicHasBitRecurrence values n := by
  intro a ha0 ha
  dsimp only
  obtain ⟨hb_le, hr_lt, ha_split⟩ := leading_bit_data n a ha0 ha
  let b := Nat.log2 a
  let r := a - 2 ^ b
  have hcancel := fabiusDyadic_add_remainder_eq_block n b r hr_lt.le
  have htaylor := hblock b r hb_le hr_lt
  change fabiusDyadic n a =
    fabiusTaylorHorner values (n - b) ((r : ℚ) / (2 : ℚ) ^ n) -
      fabiusDyadic n r
  rw [eq_sub_iff_add_eq, ha_split]
  exact hcancel.trans htaylor

/-- The precomputed inverse-power table satisfies the block Taylor identity at
grid exponent `n`; this instantiates `dyadicBlock_eq_taylor_sum` through
`fabiusTaylorHorner_eq_sum`. -/
theorem fabiusInversePowTwoTable_hasBlockTaylor (n : ℕ) :
    FabiusDyadicHasBlockTaylor (fabiusInversePowTwoTable n) n := by
  intro b r hb _hr
  rw [fabiusTaylorHorner_eq_sum n (n - b) (Nat.sub_le n b)]
  have hblock := dyadicBlock_eq_taylor_sum n b hb (r : ℚ)
  convert hblock using 1
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 2
  ring

/-- The precomputed inverse-power table satisfies the bit recurrence.  This is
the hypothesis consumed by `fabiusDyadicUnit_eq_fabiusDyadic`. -/
theorem fabiusInversePowTwoTable_hasBitRecurrence (n : ℕ) :
    FabiusDyadicHasBitRecurrence (fabiusInversePowTwoTable n) n :=
  blockTaylor_implies_bitRecurrence (fabiusInversePowTwoTable n) n
    (fabiusInversePowTwoTable_hasBlockTaylor n)

/-- On the unit dyadic grid, the executable recursion agrees with equation (32). -/
theorem fabiusDyadicUnit_eq_fabiusDyadic (n a : ℕ) (ha : a ≤ 2 ^ n) :
    fabiusDyadicUnit n a = fabiusDyadic n a :=
  fabiusDyadicUnit_eq_fabiusDyadic_of_bitRecurrence n a ha
    (fabiusInversePowTwoTable_hasBitRecurrence n)

end Fabius
