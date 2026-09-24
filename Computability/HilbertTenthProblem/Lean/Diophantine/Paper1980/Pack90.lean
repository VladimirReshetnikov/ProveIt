import Diophantine.Paper1980.Bootstrap90
import Diophantine.Paper1980.Pack93

/-!
# The three masks of the 90-operation system

Section 4 of `Papers/1980/BINARY_PRODUCT_90_PROOF.md` (the packing `(2)` is
that of `AFFINE_RADIX_95_PROOF.md`, Section 4, (20)–(21), with the radix
`B = H + b + 2` and `θ = B − 2`): once `q ≥ B > b` (a Pell conclusion), the
first mask `q² − 1 − b l` is a nonnegative integer, `T = T⁺ − 1` has the exact
three-block expansion `(q² − 1 − b l) + q² θλ + q⁴ θ l` of widths `(2, 2, 4)` in
radix `q`, and the binary no-carry packing lemma (Jones 1982, Lemmas 2.11 and
2.16) turns the central-binomial condition `n² ∣ C(2r, r)` into the three
ordinary masks

* `g & (q² − 1 − b l) = 0`,
* `(l + e q) & θλ = 0`,
* `σ & θ l = 0`,

where `&` is bitwise intersection (`τ₂(S, T) = 0` in the 1982 notation).
Both directions are proved (`masks_iff_central90`), for `q` a power of two.
The generic core `masks_iff_central_core` is shared with the 93-operation
system (`Pack93.lean`).
-/

namespace Jones1980

open Jones1982 (τ)

section Pack

variable {x V H Tindex a b c d e f g h i j k l n o q r s t w α γ η θ lam τ' φ κ μ ρ Δ β ζ σ y : ℕ}
  (hP : Pos90 x a b c d e f g h i j k l n o q r s t w α γ η θ lam τ' φ κ μ ρ Δ β ζ σ y)
  (hS : Sys90 x V H Tindex a b c d e f g h i j k l n o q r s t w α γ η θ lam τ' φ κ μ ρ Δ β ζ σ y)

include hP hS

/-- `b l + 1 ≤ q²` once `b < q`, so the first mask is a nonnegative integer. -/
theorem bl_lt_sq90 (hbq : b < q) : b * l + 1 < q ^ 2 := by
  have hl := l_lt_q90 hP hS
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hP.q; omega⟩
  have hb' : b ≤ q' := by omega
  have hl' : l ≤ q' := by omega
  have hq' : 1 ≤ q' := by have := two_le_b90 hP hS; omega
  have := Nat.mul_le_mul hb' hl'
  nlinarith

/-- The packed number `T = T⁺ − 1` in `ℕ`, and the equation for `r` in `ℕ`. -/
theorem r_nat90 (hH : 5 ≤ H) (hbq : b < q) :
    r = (g + q ^ 2 * (l + e * q + q ^ 2 * σ)) * (n ^ 2 - n) +
      ((q ^ 2 - 1 - b * l) + θ * lam * q ^ 2 + θ * l * q ^ 4 + 1) * (n ^ 2 - 1) := by
  have h7 := hS.E7
  have hbl := bl_lt_sq90 hP hS hbq
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hP.q
  have hn2 : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
  have hn1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hP.n
  have hT : ((q : ℤ) ^ 2 * (1 + θ * lam) - b * l + θ * l * q ^ 4) =
      (((q ^ 2 - 1 - b * l) + θ * lam * q ^ 2 + θ * l * q ^ 4 + 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ q ^ 2), Nat.cast_sub (by omega : b * l ≤ q ^ 2 - 1)]
    ring
  rw [hT] at h7
  have h7' : (r : ℤ) = (((g + q ^ 2 * (l + e * q + q ^ 2 * σ)) * (n ^ 2 - n) +
      ((q ^ 2 - 1 - b * l) + θ * lam * q ^ 2 + θ * l * q ^ 4 + 1) * (n ^ 2 - 1) : ℕ) : ℤ) := by
    rw [h7]; push_cast [Nat.cast_sub hn2, Nat.cast_sub hn1]; ring
  exact_mod_cast h7'

/-- The three masks are equivalent to `n² ∣ C(2r, r)`, for `q` a power of two with
`q ≥ B > b`. -/
theorem masks_iff_central90 (hH : 64 ≤ H) (hbq : b < q) (hq2 : ∃ jq, q = 2 ^ jq) :
    (τ 2 g (q ^ 2 - 1 - b * l) = 0 ∧ τ 2 (l + e * q) (θ * lam) = 0 ∧ τ 2 σ (θ * l) = 0) ↔
      n ^ 2 ∣ (2 * r).choose r := by
  obtain ⟨jq, hjq⟩ := hq2
  have hn := hS.E6
  have hnpow : n = 2 ^ (8 * jq) := by rw [hn, hjq, ← pow_mul, mul_comm]
  have hq2' : q ^ 2 = 2 ^ (2 * jq) := by rw [hjq, ← pow_mul, mul_comm]
  -- the block bounds
  have hg : g < q ^ 2 := lt_of_lt_of_le (g_lt_q90 hP hS) (Nat.le_self_pow two_ne_zero q)
  have hbl := bl_lt_sq90 hP hS hbq
  have hT1 : q ^ 2 - 1 - b * l < q ^ 2 := by omega
  have hS2 : l + e * q < q ^ 2 := S2_lt_sq90 hP hS
  have hT2 : θ * lam < q ^ 2 := by have := theta_lam_eq90 hP hS; omega
  -- the packed numbers are below `n = q^8`
  have hSl := S_lt90 hP hS
  have hTl : (q ^ 2 - 1 - b * l) + θ * lam * q ^ 2 + θ * l * q ^ 4 < q ^ 7 := by
    have h := T_lt90 hP hS (by omega)
    have hq21 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hP.q
    have hcast : ((q ^ 2 - 1 - b * l) + θ * lam * q ^ 2 + θ * l * q ^ 4 + 1 : ℤ) =
        (q : ℤ) ^ 2 * (1 + θ * lam) - b * l + θ * l * q ^ 4 := by
      push_cast [Nat.cast_sub hq21, Nat.cast_sub (by omega : b * l ≤ q ^ 2 - 1)]; ring
    have : (((q ^ 2 - 1 - b * l) + θ * lam * q ^ 2 + θ * l * q ^ 4 + 1 : ℕ) : ℤ) < (q : ℤ) ^ 7 := by
      push_cast [Nat.cast_sub hq21, Nat.cast_sub (by omega : b * l ≤ q ^ 2 - 1)]
      rw [← hcast] at h
      push_cast [Nat.cast_sub hq21, Nat.cast_sub (by omega : b * l ≤ q ^ 2 - 1)] at h
      exact h
    have := (Nat.cast_lt (α := ℤ)).1 (by push_cast at this ⊢; exact this)
    omega
  have hq7 : q ^ 7 < n := by
    rw [hn]; exact Nat.pow_lt_pow_right (by have := nine_le_q90 hP hS hH; omega) (by norm_num)
  exact masks_iff_central_core hjq hn hg hT1 hS2 hT2 hSl hTl hq7 (r_nat90 hP hS (by omega) hbq)

end Pack

end Jones1980
