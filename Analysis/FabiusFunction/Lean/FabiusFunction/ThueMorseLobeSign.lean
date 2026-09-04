import FabiusFunction.LobeSignCount
import FabiusFunction.Arithmetic
import FabiusFunction.ThueMorseBasicLemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The sign of `Φ` on the `m`-th lobe is the Thue–Morse sign

The lobe-sign count of `LobeSignCount` evaluates in closed form.
Summing the fiber sizes and applying Legendre's theorem in its
digit-sum form,

`#{lattice points ≤ m} = m + v₂(m!) = 2m − w(m)`,

where `w` is the binary digit sum.  Since `(−1)^{2m−w(m)} =
(−1)^{w(m)}`, the sign of `Φ` on the lobe `(m, m+1)` is exactly the
**Thue–Morse sign** `(−1)^{w(m)}`:

`Φ(x) = (−1)^{w(m)}·‖Φ(x)‖`  for `x ∈ (m, m+1)`.

This is the same `(−1)^{w(n)}` pattern that defines the signed global
extension `F(x) = ∑ (−1)^{w(n)} up(x − 2n − 1)` of Rvachev's function:
the Thue–Morse sign governs both the extension and the lobe signs of
its Fourier transform.

* `sum_padicValNat_Icc` — `∑_{k≤m} v₂(k) = v₂(m!)`.
* `card_lobeExceptional_add_binaryWeight` — the count `2m − w(m)`.
* `neg_one_pow_card_lobeExceptional` — the sign collapse.
* `rvachevFourierProduct_eq_thueMorse_sign_mul_norm` — **the
  Thue–Morse lobe sign**.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-- The valuations of `1, …, m` sum to the valuation of `m !`. -/
theorem sum_padicValNat_Icc (m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, padicValNat 2 k = padicValNat 2 (Nat.factorial m) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction m with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
        padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n),
        add_comm]

/-- **The closed-form count**: the lattice points at or below `m`
number `2m − w(m)`, stated additively to stay inside `ℕ`. -/
theorem card_lobeExceptional_add_binaryWeight (m : ℕ) :
    (lobeExceptional (m:ℝ)).card + binaryWeight m = 2 * m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLeg : padicValNat 2 (Nat.factorial m) = m - binaryWeight m := by
    have h := sub_one_mul_padicValNat_factorial (p := 2) m
    simpa [binaryWeight] using h
  have hw : binaryWeight m ≤ m := Nat.digit_sum_le 2 m
  have hcard : (lobeExceptional (m:ℝ)).card =
      m + padicValNat 2 (Nat.factorial m) := by
    rw [card_lobeExceptional m, Finset.sum_add_distrib,
      sum_padicValNat_Icc m, Finset.sum_const, Nat.card_Icc,
      smul_eq_mul, mul_one]
    omega
  rw [hcard, hLeg]
  omega

/-- **The sign collapse**: `(−1)^{#{lattice ≤ m}} = (−1)^{w(m)}`. -/
theorem neg_one_pow_card_lobeExceptional (m : ℕ) :
    ((-1 : ℝ)) ^ (lobeExceptional (m:ℝ)).card =
      ((-1 : ℝ)) ^ binaryWeight m :=
  neg_one_pow_eq_of_add_eq_two_mul (card_lobeExceptional_add_binaryWeight m)

/-- **The Thue–Morse lobe sign**: on the lobe `(m, m+1)`,
`Φ(x) = (−1)^{w(m)}·‖Φ(x)‖`. -/
theorem rvachevFourierProduct_eq_thueMorse_sign_mul_norm {m : ℕ}
    {x : ℝ} (hx : x ∈ Set.Ioo (m:ℝ) ((m:ℝ) + 1)) :
    rvachevFourierProduct (x : ℂ) =
      (((thueMorseSign m : ℤ) : ℝ) *
        ‖rvachevFourierProduct (x : ℂ)‖ : ℝ) := by
  have hlat := lobeZero_ne_abs_of_mem_lobe hx
  conv_lhs => rw [rvachevFourierProduct_eq_sign_mul_norm hlat]
  rw [lobeExceptional_abs_eq_of_mem_lobe hx,
    neg_one_pow_card_lobeExceptional m]
  congr 2
  rw [thueMorseSign]
  push_cast
  ring

/-- `Φ` is positive on the lobes of even binary weight and negative on
those of odd weight. -/
theorem rvachevFourierProduct_pos_of_even_weight {m : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ioo (m:ℝ) ((m:ℝ) + 1)) (hev : Even (binaryWeight m)) :
    0 < (rvachevFourierProduct (x : ℂ)).re := by
  have hlat := lobeZero_ne_abs_of_mem_lobe hx
  have hpos := norm_rvachevFourierProduct_pos_of_ne hlat
  have h := rvachevFourierProduct_eq_thueMorse_sign_mul_norm hx
  rw [h, Complex.ofReal_re, thueMorseSign]
  push_cast
  rw [hev.neg_one_pow, one_mul]
  exact hpos

end Fabius
