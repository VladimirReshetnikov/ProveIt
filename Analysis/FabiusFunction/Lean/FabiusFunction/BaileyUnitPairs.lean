import FabiusFunction.BaileyPairs
import FabiusFunction.JacobiTripleProduct
import FabiusFunction.GeometricQBinomialLagrange
import FabiusFunction.PolynomialQDerivative
import FabiusFunction.GaussianBinomialAtOne
import FabiusFunction.GaussianBinomialPalindromic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

/-!
# The two unit Bailey pairs

With `β_n = δ_{n,0}`:

* relative to `a = 1`: `α_0 = 1`, `α_n = (-1)^n q^{C(n,2)} (1 + q^n)` for `n ≥ 1`
  (`isBaileyPair_unit_one`);
* relative to `a = q`: `α_n = (-1)^n q^{C(n,2)} [2n+1]_q` (`isBaileyPair_unit_q`).

Multiplied by `(q;q)_{2n}`, respectively `(q;q)_{2n+1}`, the Bailey relations for `n ≥ 1` are
the finite identities

  `∑_{r ≤ n} α_r [2n, n-r]_q = 0`  and  `∑_{r ≤ n} (-1)^r q^{C(r,2)} (1 - q^{2r+1}) [2n+1, n-r]_q = 0`.

The first is the polynomial finite triple product `(z;q)_n ∏_{j<n} (z - q^{j+1})
= ∑_{m ≤ 2n} (-1)^{n+m} q^{e(m-n)} [2n,m]_q z^m` at `z = 1`, where the left side vanishes and
the terms `m = n ∓ r` pair up (`sum_unitBaileyAlphaOne_mul_gaussianBinomial`).  The second is
the reversed finite `q`-binomial theorem `∑_{k ≤ N} w_{N,k} z^k = ∏_{j<N} (z - q^{j+1})` for the
row `N = 2n+1` at `z = q^n`, where the factor `j = n-1` vanishes and the terms `k = n - r`,
`k = n+1+r` pair up to `(-1)^n q^{3C(n+1,2)}` times the displayed sum
(`sum_alternating_qInt_mul_gaussianBinomial`).

## Main declarations

* `unitBaileyAlphaOne`, `unitBaileyAlphaQ`, `unitBaileyBeta`.
* `sum_unitBaileyAlphaOne_mul_gaussianBinomial`, `sum_alternating_qInt_mul_gaussianBinomial`.
* `isBaileyPair_unit_one`, `isBaileyPair_unit_q`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

section CommRing

variable {R : Type*} [CommRing R]

/-- `α_n` of the unit Bailey pair relative to `a = 1`: `α_0 = 1`,
`α_n = (-1)^n q^{C(n,2)} (1 + q^n)` for `n ≥ 1`. -/
def unitBaileyAlphaOne (q : R) (n : ℕ) : R :=
  if n = 0 then 1 else (-1) ^ n * q ^ n.choose 2 * (1 + q ^ n)

/-- `α_n` of the unit Bailey pair relative to `a = q`: `α_n = (-1)^n q^{C(n,2)} [2n+1]_q`. -/
def unitBaileyAlphaQ (q : R) (n : ℕ) : R := (-1) ^ n * q ^ n.choose 2 * qInt q (2 * n + 1)

/-- The Kronecker sequence `β_n = δ_{n,0}`. -/
def unitBaileyBeta (n : ℕ) : R := if n = 0 then 1 else 0

/-- `2 C(x,2) = x (x-1)` in `ℤ`. -/
theorem two_mul_choose_two_int (x : ℕ) :
    (2 : ℤ) * (x.choose 2 : ℤ) = (x : ℤ) * ((x : ℤ) - 1) := by
  have h : ((2 * x.choose 2 + x : ℕ) : ℤ) = ((x ^ 2 : ℕ) : ℤ) := by
    rw [two_mul_choose_two_add x]
  push_cast at h
  linear_combination h

/-- The reversed finite `q`-binomial sum vanishes at `z = q^M` for `1 ≤ M ≤ N`. -/
theorem sum_weightNumerator_mul_pow_eq_zero (q : R) {N M : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    ∑ k ∈ range (N + 1), geometricQBinomialWeightNumerator q N k * (q ^ M) ^ k = 0 := by
  rw [reversed_finite_qBinomial_theorem]
  refine prod_eq_zero (i := M - 1) (mem_range.mpr (by omega)) ?_
  rw [show M - 1 + 1 = M by omega, sub_self]

/-- The finite identity behind the unit pair relative to `a = 1`:
`∑_{r ≤ n} α_r [2n, n-r]_q = 0` for `n ≥ 1`. -/
theorem sum_unitBaileyAlphaOne_mul_gaussianBinomial (q : R) {n : ℕ} (hn : 1 ≤ n) :
    ∑ r ∈ range (n + 1), unitBaileyAlphaOne q r * gaussianBinomial q (2 * n) (n - r) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have H := finite_triple_product_poly q 1 (m + 1)
  rw [finiteQPochhammerIn_one_left, zero_mul] at H
  set G : ℕ → R := fun k => (-1) ^ (m + 1 + k) * q ^ thetaExponent ((k : ℤ) - ((m + 1 : ℕ) : ℤ)) *
    gaussianBinomial q (2 * (m + 1)) k * (1 : R) ^ k with hG
  rw [← sum_range_add_sum_Ico G (show m + 1 + 1 ≤ 2 * (m + 1) + 1 by omega),
    ← sum_range_reflect G, sum_Ico_eq_sum_range,
    show 2 * (m + 1) + 1 - (m + 1 + 1) = m + 1 by omega] at H
  -- the paired terms `k = (m+1) - (j+1)` and `k = (m+1) + 1 + j`
  have hA : ∀ j ∈ range (m + 1),
      G (m + 1 + 1 - 1 - (j + 1)) + G (m + 1 + 1 + j) =
        unitBaileyAlphaOne q (j + 1) * gaussianBinomial q (2 * (m + 1)) (m + 1 - (j + 1)) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have e1 : ((m + 1 + 1 - 1 - (j + 1) : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ) = -((j + 1 : ℕ) : ℤ) := by
      rw [show m + 1 + 1 - 1 - (j + 1) = m - j by omega]
      push_cast [Nat.cast_sub hjm]
      ring
    have e2 : ((m + 1 + 1 + j : ℕ) : ℤ) - ((m + 1 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    have s1 : (-1 : R) ^ (m + 1 + (m + 1 + 1 - 1 - (j + 1))) = (-1) ^ (j + 1) := by
      rw [show m + 1 + (m + 1 + 1 - 1 - (j + 1)) = (j + 1) + 2 * (m - j) by omega, pow_add,
        pow_mul, neg_one_sq, one_pow, mul_one]
    have s2 : (-1 : R) ^ (m + 1 + (m + 1 + 1 + j)) = (-1) ^ (j + 1) := by
      rw [show m + 1 + (m + 1 + 1 + j) = (j + 1) + 2 * (m + 1) by omega, pow_add,
        pow_mul, neg_one_sq, one_pow, mul_one]
    have hsym : gaussianBinomial q (2 * (m + 1)) (m + 1 + 1 + j) =
        gaussianBinomial q (2 * (m + 1)) (m + 1 - (j + 1)) := by
      rw [← gaussianBinomial_symm q (show m + 1 + 1 + j ≤ 2 * (m + 1) by omega),
        show 2 * (m + 1) - (m + 1 + 1 + j) = m + 1 - (j + 1) by omega]
    have hch : (j + 1 + 1).choose 2 = (j + 1).choose 2 + (j + 1) := by
      have h1 := two_mul_choose_two_int (j + 1 + 1)
      have h2 := two_mul_choose_two_int (j + 1)
      push_cast at h1 h2
      zify
      linarith
    simp only [hG, one_pow, mul_one]
    rw [e1, e2, thetaExponent_neg_natCast, thetaExponent_natCast, s1, s2, hsym,
      show m + 1 + 1 - 1 - (j + 1) = m + 1 - (j + 1) by omega, hch,
      pow_add q ((j + 1).choose 2) (j + 1)]
    unfold unitBaileyAlphaOne
    rw [if_neg (Nat.succ_ne_zero j)]
    ring
  -- the middle term `k = m+1`
  have h0 : G (m + 1 + 1 - 1 - 0) =
      unitBaileyAlphaOne q 0 * gaussianBinomial q (2 * (m + 1)) (m + 1 - 0) := by
    have hs : (-1 : R) ^ (m + 1 + (m + 1)) = 1 := by
      rw [← two_mul, pow_mul, neg_one_sq, one_pow]
    simp only [hG, Nat.sub_zero, Nat.add_sub_cancel, sub_self, hs, one_pow, one_mul, mul_one]
    simp [unitBaileyAlphaOne, thetaExponent]
  calc ∑ r ∈ range (m + 1 + 1), unitBaileyAlphaOne q r * gaussianBinomial q (2 * (m + 1)) (m + 1 - r)
      = (∑ j ∈ range (m + 1),
          unitBaileyAlphaOne q (j + 1) * gaussianBinomial q (2 * (m + 1)) (m + 1 - (j + 1))) +
          unitBaileyAlphaOne q 0 * gaussianBinomial q (2 * (m + 1)) (m + 1 - 0) :=
        sum_range_succ' _ _
    _ = (∑ j ∈ range (m + 1), (G (m + 1 + 1 - 1 - (j + 1)) + G (m + 1 + 1 + j))) +
          G (m + 1 + 1 - 1 - 0) := by
        rw [h0, sum_congr rfl hA]
    _ = (∑ j ∈ range (m + 1), G (m + 1 + 1 - 1 - (j + 1)) + G (m + 1 + 1 - 1 - 0)) +
          ∑ j ∈ range (m + 1), G (m + 1 + 1 + j) := by
        rw [sum_add_distrib]
        ring
    _ = ∑ j ∈ range (m + 1 + 1), G (m + 1 + 1 - 1 - j) + ∑ j ∈ range (m + 1), G (m + 1 + 1 + j) := by
        rw [sum_range_succ' (fun j => G (m + 1 + 1 - 1 - j)) (m + 1)]
    _ = 0 := H.symm

end CommRing

section Field

variable {K : Type*} [Field K]

/-- The finite identity behind the unit pair relative to `a = q`:
`∑_{r ≤ n} (-1)^r q^{C(r,2)} (1 - q^{2r+1}) [2n+1, n-r]_q = 0` for `n ≥ 1`. -/
theorem sum_alternating_qInt_mul_gaussianBinomial (q : K) {n : ℕ} (hn : 1 ≤ n) :
    ∑ r ∈ range (n + 1), (-1) ^ r * q ^ r.choose 2 * (1 - q ^ (2 * r + 1)) *
      gaussianBinomial q (2 * n + 1) (n - r) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq0
  · -- `q = 0`: only the terms `r = 0, 1` survive, and they cancel
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sum_range_succ', sum_range_succ']
    rw [sum_eq_zero fun r _ => by
      rw [zero_pow (Nat.choose_pos (show 2 ≤ r + 1 + 1 by omega)).ne']
      ring]
    rw [gaussianBinomial_zero_left (show m + 1 - (0 + 1) ≤ 2 * (m + 1) + 1 by omega),
      gaussianBinomial_zero_left (show m + 1 - 0 ≤ 2 * (m + 1) + 1 by omega)]
    simp [Nat.choose]
  · set c : K := (-1) ^ n * q ^ (3 * (n + 1).choose 2) with hc
    have hc0 : c ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hq0)
    have H := sum_weightNumerator_mul_pow_eq_zero q (N := 2 * n + 1) (M := n) hn (by omega)
    set F : ℕ → K := fun k => geometricQBinomialWeightNumerator q (2 * n + 1) k * (q ^ n) ^ k
      with hF
    rw [← sum_range_add_sum_Ico F (show n + 1 ≤ 2 * n + 1 + 1 by omega), ← sum_range_reflect F,
      sum_Ico_eq_sum_range, show 2 * n + 1 + 1 - (n + 1) = n + 1 by omega,
      ← sum_add_distrib] at H
    have hterm : ∀ r ∈ range (n + 1),
        F (n + 1 - 1 - r) + F (n + 1 + r) =
          c * ((-1) ^ r * q ^ r.choose 2 * (1 - q ^ (2 * r + 1)) *
            gaussianBinomial q (2 * n + 1) (n - r)) := by
      intro r hr
      have hrn : r ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hr)
      have hsym : gaussianBinomial q (2 * n + 1) (n + 1 + r) =
          gaussianBinomial q (2 * n + 1) (n - r) := by
        rw [← gaussianBinomial_symm q (show n + 1 + r ≤ 2 * n + 1 by omega),
          show 2 * n + 1 - (n + 1 + r) = n - r by omega]
      have hE1 : (n + 1 + r + 1).choose 2 + n * (n - r) =
          3 * (n + 1).choose 2 + r.choose 2 + (2 * r + 1) := by
        have h1 := two_mul_choose_two_int (n + 1 + r + 1)
        have h2 := two_mul_choose_two_int (n + 1)
        have h3 := two_mul_choose_two_int r
        push_cast at h1 h2 h3
        zify [hrn]
        linarith
      have hE2 : (n - r + 1).choose 2 + n * (n + 1 + r) = 3 * (n + 1).choose 2 + r.choose 2 := by
        have h1 := two_mul_choose_two_int (n - r + 1)
        have h2 := two_mul_choose_two_int (n + 1)
        have h3 := two_mul_choose_two_int r
        push_cast [Nat.cast_sub hrn] at h1 h2 h3
        zify [hrn]
        linarith
      have hs1 : (-1 : K) ^ (n + 1 + r) = -((-1) ^ n * (-1) ^ r) := by
        rw [pow_add, pow_add, pow_one]
        ring
      have hs2 : (-1 : K) ^ n * (-1) ^ r = (-1) ^ (n - r) := by
        rw [← pow_add, show n + r = (n - r) + 2 * r by omega, pow_add, pow_mul, neg_one_sq,
          one_pow, mul_one]
      have e1 : q ^ (n + 1 + r + 1).choose 2 * q ^ (n * (n - r)) =
          q ^ (3 * (n + 1).choose 2) * q ^ r.choose 2 * q ^ (2 * r + 1) := by
        rw [← pow_add, ← pow_add, ← pow_add, hE1]
      have e2 : q ^ (n - r + 1).choose 2 * q ^ (n * (n + 1 + r)) =
          q ^ (3 * (n + 1).choose 2) * q ^ r.choose 2 := by
        rw [← pow_add, ← pow_add, hE2]
      simp only [hF, geometricQBinomialWeightNumerator]
      rw [if_pos (by omega), if_pos (by omega),
        show n + 1 - 1 - r = n - r by omega,
        show 2 * n + 1 - (n - r) = n + 1 + r by omega,
        show 2 * n + 1 - (n + 1 + r) = n - r by omega, hsym, ← pow_mul, ← pow_mul, hs1, ← hs2, hc]
      linear_combination
        (-((-1 : K) ^ n * (-1) ^ r * gaussianBinomial q (2 * n + 1) (n - r))) * e1 +
          ((-1 : K) ^ n * (-1) ^ r * gaussianBinomial q (2 * n + 1) (n - r)) * e2
    rw [sum_congr rfl hterm, ← mul_sum] at H
    exact (mul_eq_zero.mp H).resolve_left hc0

/-- **The unit Bailey pair relative to `a = 1`** (cor:unit-bailey-pairs (i)): with
`β_n = δ_{n,0}`, `α_0 = 1` and `α_n = (-1)^n q^{C(n,2)} (1 + q^n)` for `n ≥ 1`. -/
theorem isBaileyPair_unit_one {q : K} (hq : ∀ n, finiteQPochhammerIn q q n ≠ 0) :
    IsBaileyPair 1 q (unitBaileyAlphaOne q) unitBaileyBeta := by
  intro n
  simp only [one_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [unitBaileyBeta, unitBaileyAlphaOne, finiteQPochhammerIn]
  · unfold unitBaileyBeta
    rw [if_neg hn.ne']
    symm
    have hden : ∀ r ∈ range (n + 1),
        (finiteQPochhammerIn q q (n - r) * finiteQPochhammerIn q q (n + r))⁻¹ =
          gaussianBinomial q (2 * n) (n - r) / finiteQPochhammerIn q q (2 * n) := by
      intro r hr
      have hrn : r ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hr)
      have h := finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial q
        (show n - r ≤ 2 * n by omega)
      rw [show 2 * n - (n - r) = n + r by omega] at h
      have hG : gaussianBinomial q (2 * n) (n - r) ≠ 0 := by
        intro h0
        apply hq (2 * n)
        rw [h, h0, mul_zero]
      have h1 := hq (n - r)
      have h2 := hq (n + r)
      rw [h]
      field_simp
    calc ∑ r ∈ range (n + 1), unitBaileyAlphaOne q r /
          (finiteQPochhammerIn q q (n - r) * finiteQPochhammerIn q q (n + r))
        = ∑ r ∈ range (n + 1),
            unitBaileyAlphaOne q r * gaussianBinomial q (2 * n) (n - r) /
              finiteQPochhammerIn q q (2 * n) := by
          refine sum_congr rfl fun r hr => ?_
          rw [div_eq_mul_inv, hden r hr]
          ring
      _ = (∑ r ∈ range (n + 1), unitBaileyAlphaOne q r * gaussianBinomial q (2 * n) (n - r)) /
            finiteQPochhammerIn q q (2 * n) := by
          rw [sum_div]
      _ = 0 := by
          rw [sum_unitBaileyAlphaOne_mul_gaussianBinomial q hn, zero_div]

/-- **The unit Bailey pair relative to `a = q`** (cor:unit-bailey-pairs (ii)): with
`β_n = δ_{n,0}`, `α_n = (-1)^n q^{C(n,2)} [2n+1]_q`. -/
theorem isBaileyPair_unit_q {q : K} (hq : ∀ n, finiteQPochhammerIn q q n ≠ 0) :
    IsBaileyPair q q (unitBaileyAlphaQ q) unitBaileyBeta := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [unitBaileyBeta, unitBaileyAlphaQ, finiteQPochhammerIn]
  · unfold unitBaileyBeta
    rw [if_neg hn.ne']
    symm
    have h1q : (1 - q) ≠ 0 := by
      have := hq 1
      rwa [finiteQPochhammerIn, prod_range_one, pow_zero, mul_one] at this
    have hden : ∀ r ∈ range (n + 1),
        (finiteQPochhammerIn q q (n - r) * finiteQPochhammerIn (q * q) q (n + r))⁻¹ =
          (1 - q) * gaussianBinomial q (2 * n + 1) (n - r) / finiteQPochhammerIn q q (2 * n + 1) := by
      intro r hr
      have hrn : r ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hr)
      have h := finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial q
        (show n - r ≤ 2 * n + 1 by omega)
      rw [show 2 * n + 1 - (n - r) = n + r + 1 by omega, finiteQPochhammerIn_succ_shift q q (n + r)]
        at h
      have hG : gaussianBinomial q (2 * n + 1) (n - r) ≠ 0 := by
        intro h0
        apply hq (2 * n + 1)
        rw [h, h0, mul_zero]
      have hB : finiteQPochhammerIn (q * q) q (n + r) ≠ 0 := by
        intro h0
        apply hq (2 * n + 1)
        rw [h, h0]
        ring
      have h1 := hq (n - r)
      rw [h]
      field_simp
    calc ∑ r ∈ range (n + 1), unitBaileyAlphaQ q r /
          (finiteQPochhammerIn q q (n - r) * finiteQPochhammerIn (q * q) q (n + r))
        = ∑ r ∈ range (n + 1),
            (-1) ^ r * q ^ r.choose 2 * (1 - q ^ (2 * r + 1)) *
              gaussianBinomial q (2 * n + 1) (n - r) / finiteQPochhammerIn q q (2 * n + 1) := by
          refine sum_congr rfl fun r hr => ?_
          rw [div_eq_mul_inv, hden r hr]
          unfold unitBaileyAlphaQ
          rw [show (-1 : K) ^ r * q ^ r.choose 2 * qInt q (2 * r + 1) *
              ((1 - q) * gaussianBinomial q (2 * n + 1) (n - r) /
                finiteQPochhammerIn q q (2 * n + 1)) =
              (-1) ^ r * q ^ r.choose 2 * ((1 - q) * qInt q (2 * r + 1)) *
                gaussianBinomial q (2 * n + 1) (n - r) / finiteQPochhammerIn q q (2 * n + 1) by
            ring, one_sub_mul_qInt]
      _ = (∑ r ∈ range (n + 1), (-1) ^ r * q ^ r.choose 2 * (1 - q ^ (2 * r + 1)) *
            gaussianBinomial q (2 * n + 1) (n - r)) / finiteQPochhammerIn q q (2 * n + 1) := by
          rw [sum_div]
      _ = 0 := by
          rw [sum_alternating_qInt_mul_gaussianBinomial q hn, zero_div]

end Field

end Fabius
