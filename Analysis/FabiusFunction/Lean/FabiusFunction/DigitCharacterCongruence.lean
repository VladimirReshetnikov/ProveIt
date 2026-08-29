import FabiusFunction.ParityCharacter

/-!
# The lobe-sign exponent is a digit character

The exponent-sequence volume's lobe-sign law has two halves.  The
analytic half says that on the lobe `(N, N+1)` the sign of the
canonical product is `(-1)^{M_a(N)}`, where

`M_a(N) = ∑_h a_h ⌊N/2^h⌋`

counts the negative factors.  The arithmetic half is the observation
that reduces this to a *digit* character: modulo two, `⌊N/2^h⌋` is the
`h`-th binary digit of `N`, so

`M_a(N) ≡ ∑_{h ∈ bitSupport N} a_h  (mod 2)`,

and hence `(-1)^{M_a(N)} = ε_a(N)`, the weighted parity character.

This module proves the arithmetic half.  The analytic half is *not*
proved here.  The product `Φ_a` at a general admissible weight does
exist in the corpus, as `FabiusFunction.GeneralizedRvachevProduct`;
what is missing is the sign analysis on a lobe — that for
`x ∈ (N, N+1)` every factor of index at most `N` is negative and the
rest positive, which is what makes `M_a(N)` the count of negative
factors in the first place.

The bridge is `Nat.testBit_eq_decide_div_mod_eq`, which is exactly the
statement that the `h`-th bit of `N` is `⌊N/2^h⌋ mod 2`.  Everything
else is a reduction of the sum modulo two and the identification of
`{h < m | N.testBit h}` with `bitSupport N` for `N < 2^m`.

* `filter_range_testBit` — the digit set is the bit support;
* `sum_div_two_pow_mul_mod_two` — **the congruence** `M_a(N) ≡ ∑_{h ∈
  bitSupport N} a_h (mod 2)`;
* `neg_one_pow_sum_div_two_pow` — **the sign form**, `(-1)^{M_a(N)} =
  ε_a(N)`;
* `neg_one_pow_sum_div_two_pow_const_one` — at `a ≡ 1` this is the
  classical `(-1)^{∑_h ⌊N/2^h⌋} = (-1)^{w(N)}`, Legendre's count read
  modulo two.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- Two signs agree as soon as their exponents do modulo two. -/
private theorem neg_one_pow_eq_of_mod_two' {m n : ℕ}
    (h : m % 2 = n % 2) : (-1 : ℤ) ^ m = (-1) ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  conv_rhs => rw [← Nat.div_add_mod n 2]
  rw [pow_add, pow_add, pow_mul, pow_mul, neg_one_sq, one_pow, one_pow,
    one_mul, one_mul, h]

/-- The `h`-th binary digit of `N` is `⌊N/2^h⌋ mod 2`. -/
theorem testBit_iff_div_two_pow_mod_two {N h : ℕ} :
    N.testBit h = true ↔ N / 2 ^ h % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  exact decide_eq_true_iff

/-- For `N < 2 ^ m` the positions below `m` at which `N` has a one-bit
are exactly its bit support. -/
theorem filter_range_testBit {N m : ℕ} (hm : N < 2 ^ m) :
    {h ∈ range m | N.testBit h = true} = bitSupport N := by
  have hsub : bitSupport N ⊆ range m :=
    (bitSupport_subset_range_iff_lt_two_pow N m).mpr hm
  ext h
  simp only [Finset.mem_filter, mem_bitSupport]
  exact ⟨fun hh => hh.2,
    fun hh => ⟨hsub (mem_bitSupport.mpr hh), hh⟩⟩

/-- **The digit congruence.**  Modulo two, the volume's negative-factor
count `M_a(N) = ∑_h a_h ⌊N/2^h⌋` is the weight sum over the bit support
of `N`.  Only the parity of each `⌊N/2^h⌋` survives, and that parity is
the `h`-th binary digit. -/
theorem sum_div_two_pow_mul_mod_two (a : ℕ → ℕ) {N m : ℕ}
    (hm : N < 2 ^ m) :
    (∑ h ∈ range m, N / 2 ^ h * a h) % 2 =
      (∑ h ∈ bitSupport N, a h) % 2 := by
  classical
  rw [Finset.sum_nat_mod (range m) 2 (fun h => N / 2 ^ h * a h),
    Finset.sum_nat_mod (bitSupport N) 2 a, ← filter_range_testBit hm,
    Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  by_cases hb : N.testBit h = true
  · have h1 : N / 2 ^ h % 2 = 1 := testBit_iff_div_two_pow_mod_two.mp hb
    rw [if_pos hb, Nat.mul_mod, h1, one_mul]
    omega
  · have hne : N / 2 ^ h % 2 ≠ 1 := fun hc =>
      hb (testBit_iff_div_two_pow_mod_two.mpr hc)
    have h0 : N / 2 ^ h % 2 = 0 := by omega
    rw [if_neg hb, Nat.mul_mod, h0]
    omega

/-- **The sign form.**  The lobe-sign exponent is the weighted parity
character: `(-1)^{M_a(N)} = ε_a(N)`.

This is the arithmetic half of the volume's lobe-sign law.  The
analytic half — that this sign *is* `sgn Φ_a` on the lobe `(N, N+1)` —
is not proved here.  `Φ_a` itself now exists, in
`FabiusFunction.GeneralizedRvachevProduct`; what is missing is the
sign analysis on a lobe, which needs the factor-by-factor argument
that every factor with index at most `N` is negative there. -/
theorem neg_one_pow_sum_div_two_pow (a : ℕ → ℕ) {N m : ℕ}
    (hm : N < 2 ^ m) :
    (-1 : ℤ) ^ (∑ h ∈ range m, N / 2 ^ h * a h) =
      parityCharacter a N := by
  rw [parityCharacter]
  exact neg_one_pow_eq_of_mod_two' (sum_div_two_pow_mul_mod_two a hm)

/-- At the constant weight the congruence is Legendre's count read
modulo two: `(-1)^{∑_{h<m} ⌊N/2^h⌋} = (-1)^{w(N)}`, the Thue–Morse
sign. -/
theorem neg_one_pow_sum_div_two_pow_const_one {N m : ℕ}
    (hm : N < 2 ^ m) :
    (-1 : ℤ) ^ (∑ h ∈ range m, N / 2 ^ h) = thueMorseSign N := by
  have h := neg_one_pow_sum_div_two_pow (fun _ => 1) hm
  rw [parityCharacter_const_one] at h
  rw [← h]
  exact congrArg (fun k : ℕ => (-1 : ℤ) ^ k)
    (Finset.sum_congr rfl fun h _ => (Nat.mul_one _).symm)

end Fabius
