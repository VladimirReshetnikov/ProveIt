import Diophantine.Paper1982.Ratio

/-!
# Jones 1982, Lemma 2.26: adjoining a second exponential relation

The ratio system for `N² ∣ (2R).choose R` and `b pow 2` can also define
`Q = B^B₁`, provided `3 < 3B₁ ≤ B ≤ Q ≤ N ≤ R`.  Its new witnesses `C₁` and
`Δ` are positive; the alternative system also uses a positive `D₁`.

The Boolean `strong` selects the two advertised replacements for (B8):
`C = C₁ + B' + φ`, or `C = C₁ + B' + W + φ`.
All congruences are genuine congruences, so no truncated difference encodes
divisibility. The subtraction in the natural-number formulas is nonnegative
under the proved size bounds; `C26Conds.integer_iff` records the exact signed
reading of (C1)--(C3).
-/

namespace Jones1982

open Pell Diophantine JSWW1976 Jones1978

/-- The additional conditions (C1)--(C3). -/
structure C26Conds (A B B₁ Q C₁ Δ : ℕ) : Prop where
  C1 : (B ^ 2 - 1) * Q * C₁ ≡ B * (Q ^ 2 - 1) [MOD 2 * A * B - B * B - 1]
  C2 : IsSquare ((A ^ 2 - 1) * C₁ ^ 2 + 1)
  C3 : C₁ = B₁ + Δ * (A - 1)

/-- The alternative conditions (C1')--(C3'). -/
structure C26Conds' (A B B₁ Q C₁ D₁ Δ : ℕ) : Prop where
  C1 : D₁ ≡ Q + C₁ * (A - B) [MOD 2 * A * B - B * B - 1]
  C2 : D₁ ^ 2 = (A ^ 2 - 1) * C₁ ^ 2 + 1
  C3 : C₁ = B₁ + Δ * (A - 1)

/-- Exact integer semantics of (C1)--(C3); in particular, divisibility uses
signed subtraction, and the square condition is an integer square condition. -/
theorem C26Conds.integer_iff {A B B₁ Q C₁ Δ : ℕ}
    (hA : 1 < A) (hB : 0 < B) (hBA : B ≤ A) (hQ : 0 < Q) :
    C26Conds A B B₁ Q C₁ Δ ↔
      (2 * (A : ℤ) * B - B * B - 1) ∣
        B * ((Q : ℤ) ^ 2 - 1) - ((B : ℤ) ^ 2 - 1) * Q * C₁ ∧
      IsSquare (((A : ℤ) ^ 2 - 1) * C₁ ^ 2 + 1) ∧
      (C₁ : ℤ) = B₁ + Δ * ((A : ℤ) - 1) := by
  have h1 : ((B ^ 2 - 1) * Q * C₁ ≡ B * (Q ^ 2 - 1)
      [MOD 2 * A * B - B * B - 1]) ↔
      (2 * (A : ℤ) * B - B * B - 1) ∣
        B * ((Q : ℤ) ^ 2 - 1) - ((B : ℤ) ^ 2 - 1) * Q * C₁ := by
    rw [Nat.modEq_iff_dvd, J_cast hB hBA]
    push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hB), Nat.cast_sub (Nat.one_le_pow _ _ hQ)]
    rfl
  have h2 : IsSquare ((A ^ 2 - 1) * C₁ ^ 2 + 1) ↔
      IsSquare (((A : ℤ) ^ 2 - 1) * C₁ ^ 2 + 1) := by
    rw [← Int.isSquare_natCast_iff]
    push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hA.le)]
    rfl
  have h3 : C₁ = B₁ + Δ * (A - 1) ↔ (C₁ : ℤ) = B₁ + Δ * ((A : ℤ) - 1) := by
    zify [hA.le]
  constructor
  · intro h; exact ⟨h1.1 h.C1, h2.1 h.C2, h3.1 h.C3⟩
  · rintro ⟨hC1, hC2, hC3⟩; exact ⟨h1.2 hC1, h2.2 hC2, h3.2 hC3⟩

/-- The primed system also has its literal integer interpretation. -/
theorem C26Conds'.integer_iff {A B B₁ Q C₁ D₁ Δ : ℕ}
    (hA : 1 < A) (hB : 0 < B) (hBA : B ≤ A) :
    C26Conds' A B B₁ Q C₁ D₁ Δ ↔
      (2 * (A : ℤ) * B - B * B - 1) ∣ (Q : ℤ) + C₁ * ((A : ℤ) - B) - D₁ ∧
      (D₁ : ℤ) ^ 2 = ((A : ℤ) ^ 2 - 1) * C₁ ^ 2 + 1 ∧
      (C₁ : ℤ) = B₁ + Δ * ((A : ℤ) - 1) := by
  have h1 : (D₁ ≡ Q + C₁ * (A - B) [MOD 2 * A * B - B * B - 1]) ↔
      (2 * (A : ℤ) * B - B * B - 1) ∣ (Q : ℤ) + C₁ * ((A : ℤ) - B) - D₁ := by
    rw [Nat.modEq_iff_dvd, J_cast hB hBA]
    push_cast [Nat.cast_sub hBA]
    rfl
  have h2 : D₁ ^ 2 = (A ^ 2 - 1) * C₁ ^ 2 + 1 ↔
      (D₁ : ℤ) ^ 2 = ((A : ℤ) ^ 2 - 1) * C₁ ^ 2 + 1 := by
    zify [Nat.one_le_pow 2 A hA.le]
  have h3 : C₁ = B₁ + Δ * (A - 1) ↔ (C₁ : ℤ) = B₁ + Δ * ((A : ℤ) - 1) := by
    zify [hA.le]
  constructor
  · intro h; exact ⟨h1.1 h.C1, h2.1 h.C2, h3.1 h.C3⟩
  · rintro ⟨hC1, hC2, hC3⟩; exact ⟨h1.2 hC1, h2.2 hC2, h3.2 hC3⟩

/-- The size bounds used in (13), obtained from the ratio system itself. -/
theorem B25core.power_sizes {R N b h s w φ A B' C K M P U V W Y B B₁ Q : ℕ}
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbN : b ≤ N) (hs : 0 < s) (hw : 0 < w)
    (_hB₁ : 3 < 3 * B₁) (h3B₁ : 3 * B₁ ≤ B) (hBQ : B ≤ Q)
    (hQN : Q ≤ N) (hNR : N ≤ R)
    (hB : B25core R N b h s w φ A B' C K M P U V W Y) :
    ∃ _hA : 1 < A, B₁ < B' ∧ B' < A ∧ B < A ∧ B ^ (3 * B₁) < A ∧ Q ^ 3 < A := by
  obtain ⟨hU, hY, -, -, hA, -, -, -, -, -⟩ := hB.sizes hR hN hs hw
  obtain ⟨-, -, -, -, -, hRU, -, -⟩ := hB.core hR hN hbN hs hw
  have hNU : N ≤ U := by rw [hB.B9]; nlinarith
  have hMR : 64 * R ≤ M := by rw [hB.B5]; nlinarith
  have hMA : M ≤ A := by
    rw [hB.B6]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hB' : B' = 2 * R + 1 := hB.B7
  have hUA : U ^ R < A := by
    have : U ^ R ≤ R * U ^ R := Nat.le_mul_of_pos_left _ (by omega)
    omega
  refine ⟨hA, by omega, by omega, by omega, ?_, ?_⟩
  · calc B ^ (3 * B₁) ≤ U ^ (3 * B₁) := Nat.pow_le_pow_left (by omega) _
      _ ≤ U ^ R := Nat.pow_le_pow_right (by omega) (by omega)
      _ < A := hUA
  · calc Q ^ 3 ≤ U ^ 3 := Nat.pow_le_pow_left (by omega) _
      _ ≤ U ^ R := Nat.pow_le_pow_right (by omega) (by omega)
      _ < A := hUA

/-- The modified (B8) and (C2), (C3) pin down the smaller Pell index. -/
theorem B25core.small_psi {R N b h s w φ A B' C K M P U V W Y B B₁ Q C₁ Δ : ℕ}
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbN : b ≤ N) (hs : 0 < s) (hw : 0 < w)
    (hB₁ : 3 < 3 * B₁) (h3B₁ : 3 * B₁ ≤ B) (hBQ : B ≤ Q)
    (hQN : Q ≤ N) (hNR : N ≤ R) (hC₁ : 0 < C₁) (hC₁C : C₁ ≤ C)
    (hB : B25core R N b h s w φ A B' C K M P U V W Y)
    (hC2 : IsSquare ((A ^ 2 - 1) * C₁ ^ 2 + 1)) (hC3 : C₁ = B₁ + Δ * (A - 1)) :
    ∀ hA : 1 < A, C₁ = ψ hA B₁ := by
  intro hA
  obtain ⟨-, hB₁B', hB'A, -, -, -⟩ :=
    hB.power_sizes hR hN hbN hs hw hB₁ h3B₁ hBQ hQN hNR
  apply (lemma_2_23 hA hC₁ (by omega) hB₁B'.le hB'A).2
  refine ⟨by simpa only [sq] using hC2, ?_, ?_⟩
  · rw [hC3]
    show (B₁ + Δ * (A - 1)) % (A - 1) = B₁ % (A - 1)
    simp
  · rw [← hB.B14 hA]; exact hC₁C

/-- Inequality (14), in a form that also applies to the strengthened (B8). -/
theorem B25core.small_psi_gap {R N b h s w φ A B' C K M P U V W Y B₁ : ℕ}
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbN : b ≤ N) (hs : 0 < s) (hw : 0 < w)
    (hB₁ : 0 < B₁) (hB₁R : B₁ ≤ R)
    (hB : B25core R N b h s w φ A B' C K M P U V W Y)
    (hW : W = 2 ^ (2 * R + 1)) (hA : 1 < A) : ψ hA B₁ + B' + W < C := by
  obtain ⟨-, -, -, -, -, -, -, hW3⟩ := hB.core hR hN hbN hs hw
  have hB'W : B' < W := by rw [hB.B7, hW]; exact Nat.lt_two_pow_self
  have hW2 : 2 ≤ W := by rw [hB.B7] at hB'W; omega
  have h2W : 2 * W ≤ W ^ 3 := by
    calc 2 * W ≤ W * W := Nat.mul_le_mul_right W hW2
      _ = W ^ 2 := by ring
      _ ≤ W ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hB'WA : B' + W < A := by omega
  have hψ0 : 0 < ψ hA B₁ := ψ_pos_of_pos hA hB₁
  have hstep : ψ hA B₁ + A < ψ hA (B₁ + 1) := by
    have hχ := yn_lt_xn hA B₁
    have hmul : A ≤ A * ψ hA B₁ := Nat.le_mul_of_pos_right _ hψ0
    change yn hA B₁ + A < yn hA (B₁ + 1)
    rw [yn_succ]
    nlinarith
  have hmono : ψ hA (B₁ + 1) ≤ C := by
    rw [hB.B14 hA, hB.B7]
    exact (strictMono_y hA).monotone (by omega)
  omega

/-- Necessity for Lemma 2.26: the smaller Pell value fits into either modified (B8). -/
theorem exists_B26core {R N b B₁ : ℕ} (strong : Bool)
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b) (hbN : b ≤ N)
    (hB₁ : 1 < B₁) (hB₁R : B₁ ≤ R)
    (hdvd : N ^ 2 ∣ (2 * R).choose R) (hpow : ∃ k, b = 2 ^ k) :
    ∃ h s w φ A B' C K M P U V W Y C₁ Δ : ℕ,
      0 < h ∧ 0 < s ∧ 0 < w ∧ 0 < φ ∧ 0 < C₁ ∧ 0 < Δ ∧
      B25core R N b h s w (C₁ + (if strong then W else 0) + φ) A B' C K M P U V W Y ∧
      W = 2 ^ (2 * R + 1) ∧ C₁ = B₁ + Δ * (A - 1) ∧
      ∀ hA : 1 < A, C₁ = ψ hA B₁ := by
  obtain ⟨h, s, w, φ₀, A, B', C, K, M, P, U, V, W, Y, hh, hs, hw, hφ₀, hB, hW, -⟩ :=
    exists_B25core hR hN hbR hb hbN hdvd hpow
  obtain ⟨-, -, -, -, hA, -, -, -, -, -⟩ := hB.sizes hR hN hs hw
  have hC₁ : B₁ < ψ hA B₁ := lt_yn_of_two_le hA hB₁
  obtain ⟨Δ, hΔ⟩ := (Nat.modEq_iff_dvd' hC₁.le).1 (ψ_modEq hA B₁).symm
  have hΔ0 : 0 < Δ := by
    by_contra hn
    have : Δ = 0 := by omega
    rw [this, mul_zero] at hΔ
    omega
  have hgap := hB.small_psi_gap hR hN hbN hs hw (by omega) hB₁R hW hA
  have hoffset : (if strong then W else 0) ≤ W := by split <;> omega
  let φ := C - (ψ hA B₁ + B' + (if strong then W else 0))
  have hφ : 0 < φ := by dsimp [φ]; omega
  have hB8 : C = B' + (ψ hA B₁ + (if strong then W else 0) + φ) := by dsimp [φ]; omega
  refine ⟨h, s, w, φ, A, B', C, K, M, P, U, V, W, Y, ψ hA B₁, Δ,
    hh, hs, hw, hφ, by omega, hΔ0, ?_, hW, ?_, fun _ => rfl⟩
  · exact { hB with B8 := hB8 }
  · rw [mul_comm]; omega

/-- Lemma 2.26, with (C1)--(C3) and either replacement for (B8). -/
theorem lemma_2_26 {R N b B B₁ Q : ℕ} (strong : Bool)
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b) (hbN : b ≤ N)
    (hB₁ : 3 < 3 * B₁) (h3B₁ : 3 * B₁ ≤ B) (hBQ : B ≤ Q)
    (hQN : Q ≤ N) (hNR : N ≤ R) :
    (N ^ 2 ∣ (2 * R).choose R ∧ (∃ k, b = 2 ^ k) ∧ Q = B ^ B₁) ↔
      ∃ h s w φ A B' C K M P U V W Y C₁ Δ : ℕ,
        0 < h ∧ 0 < s ∧ 0 < w ∧ 0 < φ ∧ 0 < C₁ ∧ 0 < Δ ∧
        B25core R N b h s w (C₁ + (if strong then W else 0) + φ) A B' C K M P U V W Y ∧
        (V ^ 2 - 1) * W * C ≡ V * (W ^ 2 - 1) [MOD 2 * A * V - V * V - 1] ∧
        C26Conds A B B₁ Q C₁ Δ := by
  constructor
  · rintro ⟨hdvd, hpow, hQ⟩
    obtain ⟨h, s, w, φ, A, B', C, K, M, P, U, V, W, Y, C₁, Δ,
      hh, hs, hw, hφ, hC₁, hΔ, hB, hW, hC3, hCψ⟩ :=
      exists_B26core (B₁ := B₁) strong hR hN hbR hb hbN (by omega) (by omega) hdvd hpow
    obtain ⟨hA, -, -, hBA, -, -⟩ := hB.power_sizes hR hN hbN hs hw hB₁ h3B₁ hBQ hQN hNR
    refine ⟨h, s, w, φ, A, B', C, K, M, P, U, V, W, Y, C₁, Δ,
      hh, hs, hw, hφ, hC₁, hΔ, hB, ?_, ⟨?_, ?_, hC3⟩⟩
    · rw [hB.B12, hB.B14 hA, hB.B7, hW]
      exact lemma_2_22_iii hA (by norm_num) (by omega) _
    · rw [hQ, hCψ hA]
      exact lemma_2_22_iii hA (by omega) hBA.le _
    · rw [hCψ hA, sq]; exact square_of_ψ hA _
  · rintro ⟨h, s, w, φ, A, B', C, K, M, P, U, V, W, Y, C₁, Δ,
      hh, hs, hw, hφ, hC₁, hΔ, hB, hB13, hC⟩
    obtain ⟨hdvd, hpow⟩ := (lemma_2_25 hR hN hbR hb hbN).2
      ⟨h, s, w, C₁ + (if strong then W else 0) + φ, A, B', C, K, M, P, U, V, W, Y,
        hh, hs, hw, by omega, hB, hB13⟩
    obtain ⟨hA, -, -, -, hi, hii⟩ := hB.power_sizes hR hN hbN hs hw hB₁ h3B₁ hBQ hQN hNR
    refine ⟨hdvd, hpow, pow_of_congruence (by omega) (by omega) (by omega) hi hii hC.C1 ?_⟩
    exact hB.small_psi hR hN hbN hs hw hB₁ h3B₁ hBQ hQN hNR hC₁
      (by have := hB.B8; omega) hC.C2 hC.C3

/-- Lemma 2.26 with (C1')--(C3'), including positivity of the new first
Pell coordinate `D₁`, and either replacement for (B8). -/
theorem lemma_2_26' {R N b B B₁ Q : ℕ} (strong : Bool)
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b) (hbN : b ≤ N)
    (hB₁ : 3 < 3 * B₁) (h3B₁ : 3 * B₁ ≤ B) (hBQ : B ≤ Q)
    (hQN : Q ≤ N) (hNR : N ≤ R) :
    (N ^ 2 ∣ (2 * R).choose R ∧ (∃ k, b = 2 ^ k) ∧ Q = B ^ B₁) ↔
      ∃ h s w φ A B' C K M P U V W Y C₁ D₁ Δ : ℕ,
        0 < h ∧ 0 < s ∧ 0 < w ∧ 0 < φ ∧ 0 < C₁ ∧ 0 < D₁ ∧ 0 < Δ ∧
        B25core R N b h s w (C₁ + (if strong then W else 0) + φ) A B' C K M P U V W Y ∧
        (V ^ 2 - 1) * W * C ≡ V * (W ^ 2 - 1) [MOD 2 * A * V - V * V - 1] ∧
        C26Conds' A B B₁ Q C₁ D₁ Δ := by
  constructor
  · rintro ⟨hdvd, hpow, hQ⟩
    obtain ⟨h, s, w, φ, A, B', C, K, M, P, U, V, W, Y, C₁, Δ,
      hh, hs, hw, hφ, hC₁, hΔ, hB, hW, hC3, hCψ⟩ :=
      exists_B26core (B₁ := B₁) strong hR hN hbR hb hbN (by omega) (by omega) hdvd hpow
    obtain ⟨hA, -, -, hBA, -, -⟩ := hB.power_sizes hR hN hbN hs hw hB₁ h3B₁ hBQ hQN hNR
    refine ⟨h, s, w, φ, A, B', C, K, M, P, U, V, W, Y, C₁, χ hA B₁, Δ,
      hh, hs, hw, hφ, hC₁, ?_, hΔ, hB, ?_, ⟨?_, ?_, hC3⟩⟩
    · exact lt_of_le_of_lt (Nat.zero_le _) (yn_lt_xn hA B₁)
    · rw [hB.B12, hB.B14 hA, hB.B7, hW]
      exact lemma_2_22_iii hA (by norm_num) (by omega) _
    · rw [hQ, hCψ hA]
      exact χ_modEq_pow hA (by omega) hBA.le _
    · rw [hCψ hA]
      simpa only [pow_two, mul_assoc] using χ_sq hA B₁
  · rintro ⟨h, s, w, φ, A, B', C, K, M, P, U, V, W, Y, C₁, D₁, Δ,
      hh, hs, hw, hφ, hC₁, hD₁, hΔ, hB, hB13, hC⟩
    obtain ⟨hdvd, hpow⟩ := (lemma_2_25 hR hN hbR hb hbN).2
      ⟨h, s, w, C₁ + (if strong then W else 0) + φ, A, B', C, K, M, P, U, V, W, Y,
        hh, hs, hw, by omega, hB, hB13⟩
    obtain ⟨hA, -, -, -, hi, hii⟩ := hB.power_sizes hR hN hbN hs hw hB₁ h3B₁ hBQ hQN hNR
    have hCψ := hB.small_psi hR hN hbN hs hw hB₁ h3B₁ hBQ hQN hNR hC₁
      (by have := hB.B8; omega) (by rw [← hC.C2]; exact ⟨D₁, by ring⟩) hC.C3 hA
    obtain ⟨n, hDn, hCn⟩ := eq_pell_of_sq hA hC.C2
    have hn : n = B₁ := (strictMono_y hA).injective (by rw [← hCn, hCψ])
    have hcong := hC.C1
    rw [hDn, hn, hCψ] at hcong
    exact ⟨hdvd, hpow, pow_of_χ_congruence (by omega) (by omega) hi hii hA hcong⟩

end Jones1982
