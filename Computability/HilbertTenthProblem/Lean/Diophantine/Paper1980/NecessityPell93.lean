import Diophantine.Paper1980.Pell93
import Diophantine.Paper1982.PellPowerQuotient

/-!
# Necessity: the Pell witnesses of the 93-operation system (Section 7)

Given the central number `r` with `n² ∣ C(2r, r)`, `n = q⁸`, `q = 2^jq`,
`n ≤ r`, the radix `B ≤ q = B^L` and `Tindex = ψ₄(L)`, all Pell unknowns are
constructed as in `COMPOSED_99_PROOF.md`: `J = 2r + 1`, `U = 4^J`,
`Y = ⌊(U+1)^{2r}/U^r⌋`, `w = U/n²`, `s = Y/n²`, `a = Y(U+1)`, `A = a + 4`,
`P = 2UY² + 1`, `k = ψ_P(r+1)`, `2τ + 1 = χ_P(r+1)`, `c = ψ_A(J)`,
`d = χ_A(J)`, `η = c − kY`, `ζ = k − η`, `h = (k − r − 1)/(UY)`,
`κ = ψ_A(L)`, `μ = χ_A(L)`, `φ = c − κ`, the exponential quotients `γ, ρ`,
`Δ = (ψ_A(L) − ψ₄(L))/a`, and the doubled-index witnesses `f, o, j` with
the relaxed `i = (A² − 1) ψ_A(2cJ)/c²`.
-/

namespace Jones1980

open Diophantine Pell

set_option maxHeartbeats 2000000 in
/-- The Pell witnesses. -/
theorem pell_witnesses {r n q B L Tindex jq : ℕ} (hr : 2 ≤ r) (hn : n = q ^ 8) (hq : q = 2 ^ jq)
    (hjq : 1 ≤ jq) (hnr : n ≤ r) (hB : 64 ≤ B) (hBq : B ≤ q) (hL : 2 ≤ L) (hLB : 3 * L ≤ B)
    (hqL : q = B ^ L) (hT : Tindex = yn four_lt_one L) (hcentral : n ^ 2 ∣ (2 * r).choose r) :
    ∃ a c d f h i j k o s w γ η τ φ κ μ ρ Δ ζ : ℕ,
      0 < a ∧ 0 < c ∧ 0 < d ∧ 0 < f ∧ 0 < h ∧ 0 < i ∧ 0 < j ∧ 0 < k ∧ 0 < o ∧ 0 < s ∧ 0 < w ∧
      0 < γ ∧ 0 < η ∧ 0 < τ ∧ 0 < φ ∧ 0 < κ ∧ 0 < μ ∧ 0 < ρ ∧ 0 < Δ ∧ 0 < ζ ∧
      τ * (τ + 1) = (w * n ^ 2 * (s * n ^ 2) ^ 2) * (w * n ^ 2 * (s * n ^ 2) ^ 2 + 1) * k ^ 2 ∧
      c = k * (s * n ^ 2) + η ∧ k = η + ζ ∧ k = r + 1 + h * (w * n ^ 2) * (s * n ^ 2) ∧
      a = s * n ^ 2 * (w * n ^ 2 + 1) ∧ c = κ + φ ∧
      d = w * n ^ 2 + a * c + γ * (8 * a + 15) ∧
      d ^ 2 = 1 + (a ^ 2 + 8 * a + 15) * c ^ 2 ∧
      (i * c ^ 2) ^ 2 = (a ^ 2 + 8 * a + 15) * (f ^ 2 - 1) ∧
      ((o : ℤ) * f - d ^ 2) * ((o : ℤ) * f - d ^ 2 + 1) =
        (((a : ℤ) ^ 2 + 8 * a + 15) * (f ^ 2 - 1)) *
          (((a : ℤ) ^ 2 + 8 * a + 15) * (f ^ 2 - 1) - 1) * (2 * r + 1 + j * c) ^ 2 ∧
      (μ : ℤ) = q + κ * ((a : ℤ) + 4 - B) + ρ * (2 * ((a : ℤ) + 4) * B - (B : ℤ) ^ 2 - 1) ∧
      μ ^ 2 = 1 + (a ^ 2 + 8 * a + 15) * κ ^ 2 ∧
      κ = Tindex + Δ * a := by
  -- sizes
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq2 : 2 ≤ q := by omega
  have hn0 : 0 < n := by rw [hn]; positivity
  have hqn : q ≤ n := by rw [hn]; exact Nat.le_self_pow (by norm_num) q
  have hn8 : 8 * jq < n := by
    rw [hn, hq, ← pow_mul, mul_comm jq 8]; exact Nat.lt_two_pow_self
  -- `J`, `U`
  obtain ⟨J, hJ⟩ : ∃ J, J = 2 * r + 1 := ⟨_, rfl⟩
  have hJ1 : 1 < J := by omega
  have hJ2 : 2 ≤ J := by omega
  have hJodd : Odd J := ⟨r, by omega⟩
  obtain ⟨U, hU⟩ : ∃ U, U = 4 ^ J := ⟨_, rfl⟩
  have hU2 : U = 2 ^ (2 * J) := by rw [hU, pow_mul]; norm_num
  have hU0 : 0 < U := by rw [hU]; positivity
  have hU4 : 4 * 2 ^ (2 * r) < U := by
    rw [hU, hJ, pow_succ]
    have : 2 ^ (2 * r) < 4 ^ (2 * r) := Nat.pow_lt_pow_left (by norm_num) (by omega)
    omega
  have hU64 : 64 ≤ U := by
    rw [hU]
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ 4 ^ J := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hUr : r < U := by
    rw [hU]
    calc r < J := by omega
      _ < 4 ^ J := Nat.lt_pow_self (by norm_num)
  -- `Y`
  obtain ⟨Y, v, w', hsplit, hv, hY⟩ :=
    Jones1982.lemma_2_24 (R := r) (U := U) (c := 4) (by omega) (by norm_num) hU4
  -- `U^r ≤ Y`
  have hYU : U ^ r ≤ Y := by
    by_contra hlt
    push Not at hlt
    have h1 : (Y + 1) * U ^ r ≤ U ^ r * U ^ r := Nat.mul_le_mul_right _ hlt
    have h2 : U ^ r * U ^ r ≤ (U + 1) ^ (2 * r) := by
      rw [← pow_add, show r + r = 2 * r by ring]
      exact Nat.pow_le_pow_left (by omega) _
    have h3 : v < U ^ r := by omega
    nlinarith
  have hY1 : 1 ≤ Y := le_trans (Nat.one_le_pow _ _ hU0) hYU
  -- `n² ∣ U`, `n² ∣ Y`
  have hn2U : n ^ 2 ∣ U := by
    have e1 : n ^ 2 = 2 ^ (16 * jq) := by
      rw [hn, hq, ← pow_mul, ← pow_mul]; congr 1; ring
    rw [e1, hU2]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hn2Y : n ^ 2 ∣ Y := by rw [hY]; exact dvd_add hcentral (Dvd.dvd.mul_left hn2U _)
  obtain ⟨w, hw⟩ := hn2U
  obtain ⟨s, hs⟩ := hn2Y
  have hU' : U = w * n ^ 2 := by rw [hw]; ring
  have hY' : Y = s * n ^ 2 := by rw [hs]; ring
  have hw0 : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h | h
    · rw [h] at hU'; simp at hU'; omega
    · exact h
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h] at hY'; simp at hY'; omega
    · exact h
  -- `a`, `A`, `P`
  obtain ⟨a, ha⟩ : ∃ a, a = Y * (U + 1) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hA : 1 < a + 4 := by omega
  have hra : r < a := by
    rw [ha]
    calc r < U := hUr
      _ ≤ U ^ r := Nat.le_self_pow (by omega) U
      _ ≤ Y := hYU
      _ ≤ Y * (U + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hQpos : 0 < U * Y ^ 2 := by positivity
  have hPp : 1 < 2 * (U * Y ^ 2) + 1 := by omega
  -- the first Pell pair: `k = ψ_P(r+1)`, `2τ + 1 = χ_P(r+1)`
  obtain ⟨k, hk⟩ : ∃ k, k = yn hPp (r + 1) := ⟨_, rfl⟩
  have hk0 : 0 < k := by rw [hk]; exact lt_of_lt_of_le (Nat.succ_pos r) (yn_ge_n hPp (r + 1))
  have hkr : r + 1 < k := by rw [hk]; exact lt_yn_of_two_le hPp (by omega)
  have hxodd : Odd (xn hPp (r + 1)) := by
    have h := xr_odd (z := ((2 * (U * Y ^ 2) + 1 : ℕ) : ℤ)) ⟨U * Y ^ 2, by push_cast; ring⟩ (r + 1)
    rw [← xn_eq_xr hPp] at h
    exact (Int.odd_coe_nat _).1 h
  obtain ⟨τ, hτ⟩ := hxodd
  have hτ0 : 0 < τ := by
    have : 2 * (U * Y ^ 2) + 1 ≤ xn hPp (r + 1) := by
      calc 2 * (U * Y ^ 2) + 1 = (2 * (U * Y ^ 2) + 1) ^ 1 := (pow_one _).symm
        _ ≤ (2 * (U * Y ^ 2) + 1) ^ (r + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ xn hPp (r + 1) := xn_ge_a_pow hPp (r + 1)
    omega
  have E9 : τ * (τ + 1) = (U * Y ^ 2) * (U * Y ^ 2 + 1) * k ^ 2 := by
    have h := χ_sq hPp (r + 1)
    simp only [Diophantine.χ, Diophantine.ψ] at h
    rw [hτ, ← hk] at h
    have : 4 * (τ * (τ + 1)) = 4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1) * k ^ 2) := by
      have e : (2 * (U * Y ^ 2) + 1) * (2 * (U * Y ^ 2) + 1) - 1 =
          4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1)) := by
        have : (2 * (U * Y ^ 2) + 1) * (2 * (U * Y ^ 2) + 1) =
            4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1)) + 1 := by ring
        omega
      rw [e] at h
      have e2 : (2 * τ + 1) * (2 * τ + 1) = 4 * (τ * (τ + 1)) + 1 := by ring
      have e3 : 4 * (U * Y ^ 2 * (U * Y ^ 2 + 1)) * k * k =
          4 * (U * Y ^ 2 * (U * Y ^ 2 + 1) * k ^ 2) := by ring
      omega
    omega
  -- the main Pell pair
  obtain ⟨c, hc⟩ : ∃ c, c = yn hA J := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = xn hA J := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact JSWW1976.ψ_pos_of_pos hA (by omega)
  have hd0 : 0 < d := by rw [hd]; exact xn_pos' hA J
  have E15 : d ^ 2 = 1 + (a ^ 2 + 8 * a + 15) * c ^ 2 := by
    have h := χ_sq hA J
    simp only [Diophantine.χ, Diophantine.ψ] at h
    rw [← hc, ← hd] at h
    have e : (a + 4) * (a + 4) - 1 = a ^ 2 + 8 * a + 15 := by
      have : (a + 4) * (a + 4) = a ^ 2 + 8 * a + 16 := by ring
      omega
    rw [e] at h
    rw [sq, h]; ring
  -- the interval `kY < c < k(Y + 1)`
  have hlow := lower_estimate (U := U) (Y := Y) (by omega) hY1 (by omega) hJ hA ha hPp hc hk
  have hkYc : k * Y < c := by
    have h1 : k * Y * U ^ r ≤ k * (U + 1) ^ (2 * r) := by
      rw [hsplit]; nlinarith [Nat.zero_le (k * v)]
    have h2 : k * Y * U ^ r < c * U ^ r := lt_of_le_of_lt h1 hlow
    exact Nat.lt_of_mul_lt_mul_right h2
  have hUR : (0 : ℝ) < (U : ℝ) ^ r := by positivity
  have hξY' : ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r < Y + 1 := by
    rw [div_lt_iff₀ hUR]
    have h1 : ((U : ℝ) + 1) ^ (2 * r) = Y * (U : ℝ) ^ r + v := by exact_mod_cast hsplit
    have h2 : (v : ℝ) < (U : ℝ) ^ r := by
      have : v < U ^ r := by omega
      exact_mod_cast this
    rw [h1]; linarith
  have h72 : 72 * r < U + 1 := by
    have h1 := eighteen_mul_lt_pow r hr
    have : U = 4 * 16 ^ r := by rw [hU, hJ, pow_succ, mul_comm, pow_mul]; norm_num
    omega
  have h16 : 16 ≤ Y * (U + 1) := by
    calc 16 ≤ 1 * (U + 1) := by omega
      _ ≤ Y * (U + 1) := Nat.mul_le_mul_right _ hY1
  have hup := upper_estimate' (U := U) (Y := Y) (by omega) hY1 (by omega) hJ hA ha hPp hc hk hξY'
    h72 hYU h16
  have hckY : c < k * (Y + 1) := by
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have h1 : (c : ℝ) / k < Y + 1 := by
      have hv4 : (v : ℝ) * 4 < (U : ℝ) ^ r := by
        have : 4 * v < U ^ r := hv
        have : ((4 * v : ℕ) : ℝ) < ((U ^ r : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at this; linarith
      have hξ : ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r < Y + 1 / 4 := by
        rw [div_lt_iff₀ hUR]
        have h1 : ((U : ℝ) + 1) ^ (2 * r) = Y * (U : ℝ) ^ r + v := by exact_mod_cast hsplit
        rw [h1]; nlinarith
      linarith
    rw [div_lt_iff₀ hkR] at h1
    have : (c : ℝ) < ((k * (Y + 1) : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hkY1 : k * (Y + 1) = k * Y + k := by ring
  obtain ⟨η, hη⟩ : ∃ η, η = c - k * Y := ⟨_, rfl⟩
  have hη0 : 0 < η := by omega
  have E10a : c = k * Y + η := by omega
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = k - η := ⟨_, rfl⟩
  have hζ0 : 0 < ζ := by
    have : η < k := by rw [hη]; omega
    omega
  have E10b : k = η + ζ := by
    have : η < k := by rw [hη]; omega
    omega
  -- `k ≡ r + 1 (mod UY)`
  have hmod : k ≡ r + 1 [MOD 2 * (U * Y ^ 2) + 1 - 1] := by rw [hk]; exact ψ_modEq hPp (r + 1)
  have hdvd : U * Y ∣ k - (r + 1) := by
    have h1 : 2 * (U * Y ^ 2) + 1 - 1 ∣ k - (r + 1) := (Nat.modEq_iff_dvd' (by omega)).1 hmod.symm
    have h2 : U * Y ∣ 2 * (U * Y ^ 2) + 1 - 1 := by
      rw [Nat.add_sub_cancel]; exact Dvd.intro (2 * Y) (by ring)
    exact dvd_trans h2 h1
  obtain ⟨h, hh⟩ := hdvd
  have hh0 : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · rw [h0, mul_zero] at hh; omega
    · exact h0
  have E11 : k = r + 1 + h * U * Y := by
    have : k - (r + 1) = h * U * Y := by rw [hh]; ring
    omega
  -- `κ = ψ_A(L)`, `φ = c − κ`
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = yn hA L := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; exact JSWW1976.ψ_pos_of_pos hA (by omega)
  have hLJ : L < J := by omega
  have hκc : κ < c := by rw [hκ, hc]; exact strictMono_y hA hLJ
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = c - κ := ⟨_, rfl⟩
  have hφ0 : 0 < φ := by omega
  have E13 : c = κ + φ := by omega
  -- `γ`: the base-four exponent congruence
  obtain ⟨γ, hγ0, hγ⟩ := Jones1982.exists_positive_pell_power_quotient_int (A := a + 4) (B := 4)
    (L := J) hA (by norm_num) (by omega) hJ2
  have E14 : d = U + a * c + γ * (8 * a + 15) := by
    have h1 : (d : ℤ) = U + a * c + γ * (8 * a + 15) := by
      rw [hd, hU]
      have : (xn hA J : ℤ) = (χ hA J : ℤ) := rfl
      rw [this, hγ, hc]
      have : (yn hA J : ℤ) = (ψ hA J : ℤ) := rfl
      rw [this]
      push_cast
      ring
    exact_mod_cast h1
  -- `ρ`: the radix exponent congruence
  have hBA : B < a + 4 := by omega
  obtain ⟨ρ, hρ0, hρ⟩ := Jones1982.exists_positive_pell_power_quotient_int (A := a + 4) (B := B)
    (L := L) hA (by omega) hBA hL
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = xn hA L := ⟨_, rfl⟩
  have hμ0 : 0 < μ := by rw [hμ]; exact xn_pos' hA L
  have E18 : (μ : ℤ) = q + κ * ((a : ℤ) + 4 - B) + ρ * (2 * ((a : ℤ) + 4) * B - (B : ℤ) ^ 2 - 1) := by
    have hqZ : (q : ℤ) = (B : ℤ) ^ L := by rw [hqL]; push_cast; rfl
    rw [hμ, hqZ, hκ]
    have e1 : (xn hA L : ℤ) = (χ hA L : ℤ) := rfl
    have e2 : (yn hA L : ℤ) = (ψ hA L : ℤ) := rfl
    rw [e1, e2, hρ]
    push_cast
    ring
  have E19 : μ ^ 2 = 1 + (a ^ 2 + 8 * a + 15) * κ ^ 2 := by
    have h := χ_sq hA L
    simp only [Diophantine.χ, Diophantine.ψ] at h
    rw [← hκ, ← hμ] at h
    have e : (a + 4) * (a + 4) - 1 = a ^ 2 + 8 * a + 15 := by
      have : (a + 4) * (a + 4) = a ^ 2 + 8 * a + 16 := by ring
      omega
    rw [e] at h
    rw [sq, h]; ring
  -- `Δ`: the fixed index
  have hA8 : 8 ^ (L + 1) ≤ a + 4 := by
    calc 8 ^ (L + 1) ≤ 64 ^ L := by
          rw [show (64 : ℕ) = 8 ^ 2 by norm_num, ← pow_mul]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ B ^ L := Nat.pow_le_pow_left hB L
      _ = q := hqL.symm
      _ ≤ n := hqn
      _ ≤ r := hnr
      _ ≤ a + 4 := by omega
  have hκT : yn four_lt_one L < κ := by
    rw [hκ]
    show yn four_lt_one L < ψ hA L
    have hψ := pow_le_ψ_succ hA (L - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ L)] at hψ
    have hLL : L ≤ (L + 1) * (L - 1) := by
      obtain ⟨L', hL'⟩ : ∃ L', L = L' + 2 := ⟨L - 2, by omega⟩
      rw [hL', show L' + 2 - 1 = L' + 1 by omega]
      have : (L' + 2 + 1) * (L' + 1) = L' * L' + 4 * L' + 3 := by ring
      omega
    calc yn four_lt_one L < 8 ^ L := yn_four_lt L
      _ ≤ (8 ^ (L + 1)) ^ (L - 1) := by
          rw [← pow_mul]
          exact Nat.pow_le_pow_right (by norm_num) hLL
      _ ≤ (2 * (a + 4) - 1) ^ (L - 1) := Nat.pow_le_pow_left (by omega) _
      _ ≤ ψ hA L := hψ
  have hmodΔ : (yn hA L : ℤ) ≡ yn four_lt_one L [ZMOD a] := yn_add_four_modEq a hA L
  obtain ⟨Δz, hΔz⟩ := (Int.modEq_iff_dvd.1 hmodΔ.symm)
  -- `hΔz : (yn hA L : ℤ) - yn four_lt_one L = a * Δz`
  have hΔpos : 0 < Δz := by
    have h1 : (0 : ℤ) < (yn hA L : ℤ) - yn four_lt_one L := by
      have : (yn four_lt_one L : ℤ) < yn hA L := by rw [hκ] at hκT; exact_mod_cast hκT
      linarith
    rw [hΔz] at h1
    have ha' : (0 : ℤ) < a := by exact_mod_cast ha0
    exact pos_of_mul_pos_right h1 ha'.le
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℕ, (Δ : ℤ) = Δz := ⟨Δz.toNat, Int.toNat_of_nonneg hΔpos.le⟩
  have hΔ0 : 0 < Δ := by
    have : (0 : ℤ) < Δ := by rw [hΔ]; exact hΔpos
    exact_mod_cast this
  have E20 : κ = Tindex + Δ * a := by
    have h1 : (κ : ℤ) = Tindex + Δ * a := by
      rw [hκ, hT, hΔ]; linear_combination hΔz
    exact_mod_cast h1
  -- the doubled-index auxiliary witnesses, with the relaxed `i`
  obtain ⟨f, i₀, o, j, hf0, hi₀, ho0, hj0, hfi, hE17⟩ := doubled_index_necessity hA hJ1 hJodd
  obtain ⟨i, hi⟩ : ∃ i, i = (a ^ 2 + 8 * a + 15) * i₀ := ⟨_, rfl⟩
  have hi0 : 0 < i := by rw [hi]; positivity
  have hD : (a + 4) ^ 2 - 1 = a ^ 2 + 8 * a + 15 := sq_sub_one_eq a
  rw [hD, ← hc] at hfi
  have E16 : (i * c ^ 2) ^ 2 = (a ^ 2 + 8 * a + 15) * (f ^ 2 - 1) := by
    have h1 : f ^ 2 - 1 = (a ^ 2 + 8 * a + 15) * i₀ ^ 2 * c ^ 4 := by omega
    rw [h1, hi]; ring
  have E17 : ((o : ℤ) * f - d ^ 2) * ((o : ℤ) * f - d ^ 2 + 1) =
      (((a : ℤ) ^ 2 + 8 * a + 15) * (f ^ 2 - 1)) *
        (((a : ℤ) ^ 2 + 8 * a + 15) * (f ^ 2 - 1) - 1) * (2 * r + 1 + j * c) ^ 2 := by
    have e : (((a : ℤ) + 4) ^ 2 - 1) = (a : ℤ) ^ 2 + 8 * a + 15 := by ring
    have hJZ : (J : ℤ) = 2 * r + 1 := by rw [hJ]; push_cast; ring
    rw [hd, hc]
    have := hE17
    rw [show ((a + 4 : ℕ) : ℤ) = (a : ℤ) + 4 by push_cast; ring, e, hJZ] at this
    exact this
  refine ⟨a, c, d, f, h, i, j, k, o, s, w, γ, η, τ, φ, κ, μ, ρ, Δ, ζ,
    ha0, hc0, hd0, hf0, hh0, hi0, hj0, hk0, ho0, hs0, hw0, hγ0, hη0, hτ0, hφ0, hκ0, hμ0, hρ0,
    hΔ0, hζ0, ?_, ?_, E10b, ?_, ?_, E13, ?_, E15, E16, E17, E18, E19, E20⟩
  · rw [← hU', ← hY']; exact E9
  · rw [← hY']; exact E10a
  · rw [← hU', ← hY']; exact E11
  · rw [← hU', ← hY']; exact ha
  · rw [← hU']; exact E14

end Jones1980
