import FabiusFunction.RenormalizationIdentity
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Exact local factorization at the integer zeros of the sinc product

The order of an integer zero of Rvachev's Fourier product is visible before
any limiting argument: peel precisely the sinc factors which vanish there
and clear their denominators.  If the center is `2^k q`, the first `k+1`
factors turn into shifted sinc factors in the local coordinate `w`, while
the untouched tail is evaluated at `q/2 + w/2^(k+1)`.

The main identity is global in the complex variable `w`, including the
apparently singular values `w = 0` and `w = -2^k q`.  This total form is the
right reusable foundation for zero jets, reciprocal poles, and sampling
formulae.

* `mul_complexSinc_pi` is the total denominator-clearing identity.
* `mul_complexSinc_pi_add_nat` records the integral antiperiodicity of sine.
* `mul_complexSinc_pi_div_add_nat` transports that identity to an arbitrary
  nonzero complex scale.
* `rvachevFourierProduct_two_pow_mul_add_factorization` is the exact
  factorization at the center `2^k q`, without a parity hypothesis on `q`.
* `rvachevFourierProduct_two_pow_mul_odd_add_factorization` is its odd-center
  form, with the sign simplified to `-1`.
* `rvachevFourierProduct_nat_add_factorization` selects the canonical dyadic
  valuation and odd part of an arbitrary positive integer.
* `rvachevFourierProduct_int_add_factorization` covers every nonzero integer;
  the sign of the center appears only in the local tail coordinate.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

noncomputable section

/-- Clearing the removable denominator in `sinc (πz)` is valid even at
`z = 0`. -/
theorem mul_complexSinc_pi (z : ℂ) :
    z * complexSinc ((Real.pi : ℂ) * z) =
      Complex.sin ((Real.pi : ℂ) * z) / Real.pi := by
  by_cases hz : z = 0
  · subst z
    simp [complexSinc]
  · have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [complexSinc, if_neg (mul_ne_zero hpi hz)]
    field_simp

/-- Translating the argument of `sinc (πz)` by a natural number contributes
the corresponding alternating sign after its denominator is cleared. -/
theorem mul_complexSinc_pi_add_nat (n : ℕ) (z : ℂ) :
    ((n : ℂ) + z) *
        complexSinc ((Real.pi : ℂ) * ((n : ℂ) + z)) =
      (-1 : ℂ) ^ n * z * complexSinc ((Real.pi : ℂ) * z) := by
  have harg :
      (Real.pi : ℂ) * ((n : ℂ) + z) =
        (Real.pi : ℂ) * z + (n : ℕ) * (Real.pi : ℂ) := by
    ring
  calc
    ((n : ℂ) + z) *
        complexSinc ((Real.pi : ℂ) * ((n : ℂ) + z)) =
        Complex.sin ((Real.pi : ℂ) * ((n : ℂ) + z)) / Real.pi :=
      mul_complexSinc_pi ((n : ℂ) + z)
    _ = (-1 : ℂ) ^ n * Complex.sin ((Real.pi : ℂ) * z) / Real.pi := by
      rw [harg, Complex.sin_antiperiodic.add_nat_mul_eq]
    _ = (-1 : ℂ) ^ n * z *
        complexSinc ((Real.pi : ℂ) * z) := by
      calc
        (-1 : ℂ) ^ n * Complex.sin ((Real.pi : ℂ) * z) / Real.pi =
            (-1 : ℂ) ^ n *
              (Complex.sin ((Real.pi : ℂ) * z) / Real.pi) := by ring
        _ = (-1 : ℂ) ^ n *
              (z * complexSinc ((Real.pi : ℂ) * z)) := by
          rw [mul_complexSinc_pi]
        _ = _ := by ring

/-- The scaled integer-shift law.  No positivity or reality assumption on the
scale is needed: an arbitrary nonzero complex scale carries the same lattice
factorization. -/
theorem mul_complexSinc_pi_div_add_nat {a : ℂ} (ha : a ≠ 0)
    (n : ℕ) (z : ℂ) :
    (a * (n : ℂ) + z) *
        complexSinc ((Real.pi : ℂ) * (a * (n : ℂ) + z) / a) =
      (-1 : ℂ) ^ n * z *
        complexSinc ((Real.pi : ℂ) * z / a) := by
  have hcenter : a * (n : ℂ) + z = a * ((n : ℂ) + z / a) := by
    field_simp
  have harg :
      (Real.pi : ℂ) * (a * ((n : ℂ) + z / a)) / a =
        (Real.pi : ℂ) * ((n : ℂ) + z / a) := by
    field_simp
  calc
    (a * (n : ℂ) + z) *
        complexSinc ((Real.pi : ℂ) * (a * (n : ℂ) + z) / a) =
        a * (((n : ℂ) + z / a) *
          complexSinc ((Real.pi : ℂ) * ((n : ℂ) + z / a))) := by
      rw [hcenter, harg]
      ring
    _ = a * ((-1 : ℂ) ^ n * (z / a) *
        complexSinc ((Real.pi : ℂ) * (z / a))) := by
      rw [mul_complexSinc_pi_add_nat]
    _ = (-1 : ℂ) ^ n * z *
        complexSinc ((Real.pi : ℂ) * z / a) := by
      have harg' :
          (Real.pi : ℂ) * (z / a) = (Real.pi : ℂ) * z / a := by ring
      rw [harg']
      field_simp

private lemma sum_range_two_pow_local (n : ℕ) :
    ∑ h ∈ range n, 2 ^ h = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

private lemma sum_two_pow_reverse_mul (k q : ℕ) :
    ∑ h ∈ range (k + 1), 2 ^ (k - h) * q =
      (2 ^ (k + 1) - 1) * q := by
  calc
    ∑ h ∈ range (k + 1), 2 ^ (k - h) * q =
        (∑ h ∈ range (k + 1), 2 ^ (k - h)) * q := by
      rw [Finset.sum_mul]
    _ = (∑ h ∈ range (k + 1), 2 ^ h) * q := by
      rw [Finset.sum_flip]
    _ = (2 ^ (k + 1) - 1) * q := by rw [sum_range_two_pow_local]

private lemma odd_two_pow_succ_sub_one (k : ℕ) :
    Odd (2 ^ (k + 1) - 1) := by
  refine ⟨2 ^ k - 1, ?_⟩
  rw [pow_succ]
  have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

private lemma prod_neg_one_pow_dyadic_quotients (k q : ℕ) :
    ∏ h ∈ range (k + 1),
        (-1 : ℂ) ^ (2 ^ (k - h) * q) =
      (-1 : ℂ) ^ q := by
  rw [Finset.prod_pow_eq_pow_sum, sum_two_pow_reverse_mul,
    pow_mul, (odd_two_pow_succ_sub_one k).neg_one_pow]

/-- **Exact dyadic-center local factorization.**  At the center `2^k q`,
clearing the first `k+1` sinc denominators exposes the local zero factor
`w^(k+1)`.  The sign is retained as `(-1)^q`, so this identity also covers
even `q` and the degenerate center `q = 0`. -/
theorem rvachevFourierProduct_two_pow_mul_add_factorization
    (k q : ℕ) (w : ℂ) :
    (((2 : ℂ) ^ k * (q : ℂ) + w) ^ (k + 1)) *
        rvachevFourierProduct ((2 : ℂ) ^ k * (q : ℂ) + w) =
      (-1 : ℂ) ^ q * w ^ (k + 1) *
        (∏ h ∈ range (k + 1),
          complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) *
        rvachevFourierProduct
          ((q : ℂ) / 2 + w / (2 : ℂ) ^ (k + 1)) := by
  let center : ℂ := (2 : ℂ) ^ k * (q : ℂ)
  have hfactor (h : ℕ) (hh : h ∈ range (k + 1)) :
      (center + w) *
          complexSinc ((Real.pi : ℂ) * (center + w) / (2 : ℂ) ^ h) =
        (-1 : ℂ) ^ (2 ^ (k - h) * q) * w *
          complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h) := by
    have hhk : h ≤ k := Nat.le_of_lt_succ (mem_range.mp hh)
    have hnat : 2 ^ h * (2 ^ (k - h) * q) = 2 ^ k * q := by
      calc
        2 ^ h * (2 ^ (k - h) * q) =
            (2 ^ h * 2 ^ (k - h)) * q := by ring
        _ = 2 ^ (h + (k - h)) * q := by rw [← pow_add]
        _ = 2 ^ k * q := by rw [Nat.add_sub_of_le hhk]
    have hcenter :
        (2 : ℂ) ^ h * ((2 ^ (k - h) * q : ℕ) : ℂ) = center := by
      dsimp [center]
      exact_mod_cast hnat
    simpa only [hcenter] using
      (mul_complexSinc_pi_div_add_nat
        (pow_ne_zero h (by norm_num : (2 : ℂ) ≠ 0))
        (2 ^ (k - h) * q) w)
  have htail :
      (center + w) / (2 : ℂ) ^ (k + 1) =
        (q : ℂ) / 2 + w / (2 : ℂ) ^ (k + 1) := by
    dsimp [center]
    field_simp
    ring
  change (center + w) ^ (k + 1) *
      rvachevFourierProduct (center + w) = _
  rw [rvachevFourierProduct_shell (k + 1) (center + w), htail]
  calc
    (center + w) ^ (k + 1) *
        ((∏ h ∈ range (k + 1),
          complexSinc ((Real.pi : ℂ) * (center + w) / (2 : ℂ) ^ h)) *
          rvachevFourierProduct
            ((q : ℂ) / 2 + w / (2 : ℂ) ^ (k + 1))) =
        (∏ h ∈ range (k + 1),
          ((center + w) *
            complexSinc
              ((Real.pi : ℂ) * (center + w) / (2 : ℂ) ^ h))) *
          rvachevFourierProduct
            ((q : ℂ) / 2 + w / (2 : ℂ) ^ (k + 1)) := by
      rw [Finset.pow_eq_prod_const, ← mul_assoc,
        ← Finset.prod_mul_distrib]
    _ = (∏ h ∈ range (k + 1),
          ((-1 : ℂ) ^ (2 ^ (k - h) * q) * w *
            complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h))) *
          rvachevFourierProduct
            ((q : ℂ) / 2 + w / (2 : ℂ) ^ (k + 1)) := by
      congr 1
      exact Finset.prod_congr rfl hfactor
    _ = (-1 : ℂ) ^ q * w ^ (k + 1) *
        (∏ h ∈ range (k + 1),
          complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) *
        rvachevFourierProduct
          ((q : ℂ) / 2 + w / (2 : ℂ) ^ (k + 1)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
        prod_neg_one_pow_dyadic_quotients]
      simp only [Finset.prod_const, Finset.card_range]

/-- At a center `2^k q` with odd `q`, the exact local factorization has the
constant sign `-1`. -/
theorem rvachevFourierProduct_two_pow_mul_odd_add_factorization
    (k q : ℕ) (hq : Odd q) (w : ℂ) :
    (((2 : ℂ) ^ k * (q : ℂ) + w) ^ (k + 1)) *
        rvachevFourierProduct ((2 : ℂ) ^ k * (q : ℂ) + w) =
      -w ^ (k + 1) *
        (∏ h ∈ range (k + 1),
          complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) *
        rvachevFourierProduct
          ((q : ℂ) / 2 + w / (2 : ℂ) ^ (k + 1)) := by
  rw [rvachevFourierProduct_two_pow_mul_add_factorization,
    hq.neg_one_pow]
  ring

/-- **Canonical factorization at a positive integer.**  The exponent is the
exact dyadic valuation plus one, and `divMaxPow m 2` supplies the canonical odd
part. -/
theorem rvachevFourierProduct_nat_add_factorization
    (m : ℕ) (hm : m ≠ 0) (w : ℂ) :
    (((m : ℂ) + w) ^ (padicValNat 2 m + 1)) *
        rvachevFourierProduct ((m : ℂ) + w) =
      -w ^ (padicValNat 2 m + 1) *
        (∏ h ∈ range (padicValNat 2 m + 1),
          complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) *
        rvachevFourierProduct
          (((Nat.divMaxPow m 2 : ℕ) : ℂ) / 2 +
            w / (2 : ℂ) ^ (padicValNat 2 m + 1)) := by
  have hodd : Odd (Nat.divMaxPow m 2) :=
    Nat.not_even_iff_odd.mp
      (mt Even.two_dvd (Nat.not_dvd_divMaxPow (by norm_num) hm))
  have hdecomp : 2 ^ padicValNat 2 m * Nat.divMaxPow m 2 = m :=
    Nat.pow_padicValNat_mul_divMaxPow 2 m
  have hdecompC :
      (2 : ℂ) ^ padicValNat 2 m * (Nat.divMaxPow m 2 : ℂ) = (m : ℂ) := by
    exact_mod_cast hdecomp
  simpa only [hdecompC] using
    rvachevFourierProduct_two_pow_mul_odd_add_factorization
      (padicValNat 2 m) (Nat.divMaxPow m 2) hodd w

/-- **Canonical factorization at any nonzero integer.**  Passing to the
absolute value chooses the dyadic valuation and odd core.  Since `Φ` and the
local sinc prefix are even, the sign of the integer center appears only in
the final tail coordinate. -/
theorem rvachevFourierProduct_int_add_factorization
    (m : ℤ) (hm : m ≠ 0) (w : ℂ) :
    (((m : ℂ) + w) ^ (padicValNat 2 m.natAbs + 1)) *
        rvachevFourierProduct ((m : ℂ) + w) =
      -w ^ (padicValNat 2 m.natAbs + 1) *
        (∏ h ∈ range (padicValNat 2 m.natAbs + 1),
          complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) *
        rvachevFourierProduct
          (((Nat.divMaxPow m.natAbs 2 : ℕ) : ℂ) / 2 +
            (Int.sign m : ℂ) * w /
              (2 : ℂ) ^ (padicValNat 2 m.natAbs + 1)) := by
  cases m with
  | ofNat n =>
      cases n with
      | zero => simp at hm
      | succ n =>
          have hn : n + 1 ≠ 0 := by omega
          simpa only [Int.ofNat_eq_natCast, Int.natAbs_natCast,
            Int.sign_natCast_of_ne_zero hn, Int.cast_natCast,
            Int.cast_one, one_mul] using
            rvachevFourierProduct_nat_add_factorization
              (n + 1) hn w
  | negSucc n =>
      let N : ℕ := n + 1
      let d : ℕ := padicValNat 2 N + 1
      let q : ℕ := Nat.divMaxPow N 2
      have hpos :=
        rvachevFourierProduct_nat_add_factorization N (by omega) (-w)
      have hfourier :
          rvachevFourierProduct (-(N : ℂ) + w) =
            rvachevFourierProduct ((N : ℂ) - w) := by
        rw [show -(N : ℂ) + w = -((N : ℂ) - w) by ring,
          rvachevFourierProduct_neg]
      have hcenterpow :
          (-(N : ℂ) + w) ^ d =
            (-1 : ℂ) ^ d * ((N : ℂ) - w) ^ d := by
        rw [show -(N : ℂ) + w = -((N : ℂ) - w) by ring,
          neg_pow]
      have hprefix :
          (∏ h ∈ range d,
            complexSinc ((Real.pi : ℂ) * (-w) / (2 : ℂ) ^ h)) =
          ∏ h ∈ range d,
            complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h) := by
        apply Finset.prod_congr rfl
        intro h hh
        rw [show (Real.pi : ℂ) * (-w) / (2 : ℂ) ^ h =
            -((Real.pi : ℂ) * w / (2 : ℂ) ^ h) by ring,
          complexSinc_neg]
      have hnegpow : (-w) ^ d = (-1 : ℂ) ^ d * w ^ d := by
        rw [show -w = (-1 : ℂ) * w by ring, mul_pow]
      have hsign : (-1 : ℂ) ^ d * (-1 : ℂ) ^ d = 1 := by
        rw [← pow_add, Even.neg_one_pow ⟨d, rfl⟩]
      simp only [Int.natAbs_negSucc, Int.cast_negSucc,
        Int.sign_negSucc, Int.cast_neg, Int.cast_one, neg_one_mul]
      change (-(N : ℂ) + w) ^ d *
          rvachevFourierProduct (-(N : ℂ) + w) =
        -w ^ d *
          (∏ h ∈ range d,
            complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) *
          rvachevFourierProduct
            ((q : ℂ) / 2 + (-w) / (2 : ℂ) ^ d)
      change ((N : ℂ) - w) ^ d *
          rvachevFourierProduct ((N : ℂ) - w) =
        -(-w) ^ d *
          (∏ h ∈ range d,
            complexSinc ((Real.pi : ℂ) * (-w) / (2 : ℂ) ^ h)) *
          rvachevFourierProduct
            ((q : ℂ) / 2 + (-w) / (2 : ℂ) ^ d) at hpos
      calc
        (-(N : ℂ) + w) ^ d *
            rvachevFourierProduct (-(N : ℂ) + w) =
            (-1 : ℂ) ^ d *
              (((N : ℂ) - w) ^ d *
                rvachevFourierProduct ((N : ℂ) - w)) := by
          rw [hcenterpow, hfourier]
          ring
        _ = (-1 : ℂ) ^ d *
              (-(-w) ^ d *
                (∏ h ∈ range d,
                  complexSinc
                    ((Real.pi : ℂ) * (-w) / (2 : ℂ) ^ h)) *
                rvachevFourierProduct
                  ((q : ℂ) / 2 + (-w) / (2 : ℂ) ^ d)) := by
          rw [hpos]
        _ = -w ^ d *
              (∏ h ∈ range d,
                complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) *
              rvachevFourierProduct
                ((q : ℂ) / 2 + (-w) / (2 : ℂ) ^ d) := by
          rw [hnegpow, hprefix]
          calc
            (-1 : ℂ) ^ d *
                (-((-1 : ℂ) ^ d * w ^ d) *
                  (∏ h ∈ range d,
                    complexSinc
                      ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) *
                  rvachevFourierProduct
                    ((q : ℂ) / 2 + (-w) / (2 : ℂ) ^ d)) =
                -((-1 : ℂ) ^ d * (-1 : ℂ) ^ d) * w ^ d *
                  (∏ h ∈ range d,
                    complexSinc
                      ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) *
                  rvachevFourierProduct
                    ((q : ℂ) / 2 + (-w) / (2 : ℂ) ^ d) := by ring
            _ = _ := by rw [hsign]; ring

end

end Fabius
