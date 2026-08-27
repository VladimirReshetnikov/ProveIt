import FabiusFunction.LobeSignCount
import FabiusFunction.Arithmetic
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
      have hIcc : Finset.Icc 1 (n + 1) =
          insert (n + 1) (Finset.Icc 1 n) := by
        ext k
        rw [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Icc]
        constructor
        · rintro ⟨h1, h2⟩
          rcases eq_or_lt_of_le h2 with rfl | h
          · exact Or.inl rfl
          · exact Or.inr ⟨h1, by omega⟩
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨by omega, le_refl _⟩
          · exact ⟨h1, by omega⟩
      have hnot : (n + 1) ∉ Finset.Icc 1 n := by
        rw [Finset.mem_Icc]
        omega
      rw [hIcc, Finset.sum_insert hnot, ih, Nat.factorial_succ,
        padicValNat.mul (Nat.succ_ne_zero n)
          (Nat.factorial_ne_zero n)]

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
      ((-1 : ℝ)) ^ binaryWeight m := by
  set c : ℕ := (lobeExceptional (m:ℝ)).card with hc
  set w : ℕ := binaryWeight m with hw
  have hsum : c + w = 2 * m := card_lobeExceptional_add_binaryWeight m
  have h1 : ((-1 : ℝ)) ^ c * ((-1 : ℝ)) ^ w = 1 := by
    rw [← pow_add, hsum, pow_mul]
    norm_num
  have h2 : ((-1 : ℝ)) ^ w * ((-1 : ℝ)) ^ w = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc ((-1 : ℝ)) ^ c
      = ((-1 : ℝ)) ^ c * (((-1 : ℝ)) ^ w * ((-1 : ℝ)) ^ w) := by
        rw [h2, mul_one]
    _ = (((-1 : ℝ)) ^ c * ((-1 : ℝ)) ^ w) * ((-1 : ℝ)) ^ w := by ring
    _ = ((-1 : ℝ)) ^ w := by rw [h1, one_mul]

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
