import Diophantine.Paper1980.Bootstrap93
import Diophantine.Paper1982.Carries

/-!
# The three masks of the 93-operation system

Section 4, (20)–(21), of `Papers/1980/AFFINE_RADIX_95_PROOF.md`: once
`q ≥ B > b` (a Pell conclusion), the first mask `q² − 1 − b l` is a
nonnegative integer, `T = T⁺ − 1` has the exact three-block expansion
`(q² − 1 − b l) + q² θλ + q⁴ θ l` of widths `(2, 2, 4)` in radix `q`, and the
binary no-carry packing lemma (Jones 1982, Lemmas 2.11 and 2.16) turns the
central-binomial condition `n² ∣ C(2r, r)` into the three ordinary masks

* `g & (q² − 1 − b l) = 0`,
* `(l + e q) & θλ = 0`,
* `σ & θ l = 0`,

where `&` is bitwise intersection (`τ₂(S, T) = 0` in the 1982 notation).
Both directions are proved (`masks_iff_central`), for `q` a power of two.
-/

namespace Jones1980

open Jones1982 (τ)

/-- The three masks are equivalent to `n² ∣ C(2r, r)`: the core packing statement, with the
block bounds as hypotheses. -/
theorem masks_iff_central_core {g l e q σ θ lam b n r jq : ℕ} (hjq : q = 2 ^ jq) (hn : n = q ^ 8)
    (hg : g < q ^ 2) (hT1 : q ^ 2 - 1 - b * l < q ^ 2) (hS2 : l + e * q < q ^ 2)
    (hT2 : θ * lam < q ^ 2) (hSl : g + q ^ 2 * (l + e * q + q ^ 2 * σ) < q ^ 7)
    (hTl : (q ^ 2 - 1 - b * l) + θ * lam * q ^ 2 + θ * l * q ^ 4 < q ^ 7) (hq7 : q ^ 7 < n)
    (hr : r = (g + q ^ 2 * (l + e * q + q ^ 2 * σ)) * (n ^ 2 - n) +
      ((q ^ 2 - 1 - b * l) + θ * lam * q ^ 2 + θ * l * q ^ 4 + 1) * (n ^ 2 - 1)) :
    (τ 2 g (q ^ 2 - 1 - b * l) = 0 ∧ τ 2 (l + e * q) (θ * lam) = 0 ∧ τ 2 σ (θ * l) = 0) ↔
      n ^ 2 ∣ (2 * r).choose r := by
  have hnpow : n = 2 ^ (8 * jq) := by rw [hn, hjq, ← pow_mul, mul_comm]
  have hq2' : q ^ 2 = 2 ^ (2 * jq) := by rw [hjq, ← pow_mul, mul_comm]
  -- the three-block form of `S` and `T`
  have hSform : g + q ^ 2 * (l + e * q + q ^ 2 * σ) =
      g + (l + e * q) * 2 ^ (2 * jq) + σ * 2 ^ (2 * jq) * 2 ^ (2 * jq) := by
    rw [← hq2']; ring
  have hTform : (q ^ 2 - 1 - b * l) + θ * lam * q ^ 2 + θ * l * q ^ 4 =
      (q ^ 2 - 1 - b * l) + θ * lam * 2 ^ (2 * jq) + θ * l * 2 ^ (2 * jq) * 2 ^ (2 * jq) := by
    rw [← hq2']; ring
  -- Lemma 2.16 for `N = n`
  have h216 := Jones1982.lemma_2_16 (α := 8 * jq)
    (S := g + q ^ 2 * (l + e * q + q ^ 2 * σ))
    (T := (q ^ 2 - 1 - b * l) + θ * lam * q ^ 2 + θ * l * q ^ 4) (R := r)
    (by rw [← hnpow]; omega) (by rw [← hnpow]; omega) (by rw [← hnpow]; exact hr)
  rw [← hnpow] at h216
  -- Lemma 2.11 for the three blocks
  have h211 := Jones1982.lemma_2_11_three (k₁ := 2 * jq) (k₂ := 2 * jq)
    (S₁ := g) (S₂ := l + e * q) (S₃ := σ)
    (T₁ := q ^ 2 - 1 - b * l) (T₂ := θ * lam) (T₃ := θ * l)
    (by rw [← hq2']; exact hg) (by rw [← hq2']; exact hT1)
    (by rw [← hq2']; exact hS2) (by rw [← hq2']; exact hT2)
  rw [h211, ← hSform, ← hTform]
  exact h216


section Pack

variable {x V H Tindex a b c d e f g h i j k l n o q r s t w α γ η θ lam τ' φ κ μ ρ Δ β ζ σ Ω : ℕ}
  (hP : Pos93 x a b c d e f g h i j k l n o q r s t w α γ η θ lam τ' φ κ μ ρ Δ β ζ σ Ω)
  (hS : Sys93 x V H Tindex a b c d e f g h i j k l n o q r s t w α γ η θ lam τ' φ κ μ ρ Δ β ζ σ Ω)

include hP hS

/-- `b l + 1 ≤ q²` once `b < q`, so the first mask is a nonnegative integer. -/
theorem bl_lt_sq (hbq : b < q) : b * l + 1 < q ^ 2 := by
  have hl := l_lt_q hP hS
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hP.q; omega⟩
  have hb' : b ≤ q' := by omega
  have hl' : l ≤ q' := by omega
  have hq' : 1 ≤ q' := by have := two_le_b hP hS; omega
  have := Nat.mul_le_mul hb' hl'
  nlinarith

/-- The packed number `T = T⁺ − 1` in `ℕ`, and the equation for `r` in `ℕ`. -/
theorem r_nat (hH : 5 ≤ H) (hbq : b < q) :
    r = (g + q ^ 2 * (l + e * q + q ^ 2 * σ)) * (n ^ 2 - n) +
      ((q ^ 2 - 1 - b * l) + θ * lam * q ^ 2 + θ * l * q ^ 4 + 1) * (n ^ 2 - 1) := by
  have h7 := hS.E7
  have hbl := bl_lt_sq hP hS hbq
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
theorem masks_iff_central (hH : 64 ≤ H) (hbq : b < q) (hq2 : ∃ jq, q = 2 ^ jq) :
    (τ 2 g (q ^ 2 - 1 - b * l) = 0 ∧ τ 2 (l + e * q) (θ * lam) = 0 ∧ τ 2 σ (θ * l) = 0) ↔
      n ^ 2 ∣ (2 * r).choose r := by
  obtain ⟨jq, hjq⟩ := hq2
  have hn := hS.E6
  have hnpow : n = 2 ^ (8 * jq) := by rw [hn, hjq, ← pow_mul, mul_comm]
  have hq2' : q ^ 2 = 2 ^ (2 * jq) := by rw [hjq, ← pow_mul, mul_comm]
  -- the block bounds
  have hg : g < q ^ 2 := lt_of_lt_of_le (g_lt_q hP hS) (Nat.le_self_pow two_ne_zero q)
  have hbl := bl_lt_sq hP hS hbq
  have hT1 : q ^ 2 - 1 - b * l < q ^ 2 := by omega
  have hS2 : l + e * q < q ^ 2 := S2_lt_sq hP hS
  have hT2 : θ * lam < q ^ 2 := by have := theta_lam_eq hP hS; omega
  -- the packed numbers are below `n = q^8`
  have hSl := S_lt hP hS
  have hTl : (q ^ 2 - 1 - b * l) + θ * lam * q ^ 2 + θ * l * q ^ 4 < q ^ 7 := by
    have h := T_lt hP hS (by omega)
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
    rw [hn]; exact Nat.pow_lt_pow_right (by have := nine_le_q hP hS hH; omega) (by norm_num)
  exact masks_iff_central_core hjq hn hg hT1 hS2 hT2 hSl hTl hq7 (r_nat hP hS (by omega) hbq)

end Pack

end Jones1980
