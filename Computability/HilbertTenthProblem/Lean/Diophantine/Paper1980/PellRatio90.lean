import Diophantine.Paper1980.PellDoubled
import Diophantine.Paper1982.Ratio

/-!
# The ratio block of the 90-operation system (Pell base `A = a + 2`)

With `U = w n²`, `Y = s n²`, `Q = U Y²`, `P = 2Q + 1`, `a = Y(U + 1)`, `A = a + 2`,
`J = 2r + 1`, the block

* `E9 : τ(τ + 1) = Q(Q + 1) k²` (so `2τ + 1, k` is a Pell pair for `P`),
* `E11 : k = r + 1 + h U Y`,
* `E10a/b : c = k Y + η`, `k = η + ζ` (the interval `Y < c/k < Y + 1`),

together with `c = ψ_A(J)` from the doubled-index block, gives

1. `k = ψ_P(r + 1)` (`k_index`), by the congruence `ψ_P(t) ≡ t (mod U Y)` and growth;
2. `U^r ≤ Y` (`Y_lower`), since `c/k > ξ := (U+1)^(2r)/U^r` and `c/k < Y + 1`;
3. after `U = 4^J` is known, `c/k < ξ + 1/2`, so `Y = ⌊ξ⌋ ≡ C(2r, r) (mod U)`
   (`Y_eq_floor`), hence `n² ∣ C(2r, r)` (`central_dvd`).

This is the argument of `PELL_COMMON_WITNESS_PROOF.md`, `PELL_UNIT_SCALE_PROOF.md` and
`PELL_SHARED_RATIO_PRODUCT_PROOF.md`, with the bounds redone for the shifted
parameters `A = Y(U+1) + 2` and `P = 2UY² + 1`.
-/

namespace Jones1980

namespace Ratio90

open Diophantine Pell

/-! ### The integer half -/

/-- `2P (U+1)² < (2A − 1)² U` for `A = Y(U+1) + 2`, `P = 2UY² + 1`. -/
theorem lower_key {U Y : ℕ} (hU : 1 ≤ U) (hY : 1 ≤ Y) :
    2 * (2 * (U * Y ^ 2) + 1) * (U + 1) ^ 2 < (2 * (Y * (U + 1) + 2) - 1) ^ 2 * U := by
  have e : 2 * (Y * (U + 1) + 2) - 1 = 2 * (Y * (U + 1)) + 3 := by omega
  rw [e]
  have h1 : U * (U + 1) ≤ U * Y * (U + 1) := by
    have := Nat.mul_le_mul_right (U + 1) (Nat.mul_le_mul_left U hY)
    simpa using this
  nlinarith [h1, hU]

/-- `4A < 2P − 1` for `Y ≥ 2`, `U ≥ 4`. -/
theorem two_A_lt {U Y : ℕ} (hU : 4 ≤ U) (hY : 2 ≤ Y) :
    4 * (Y * (U + 1) + 2) < 2 * (2 * (U * Y ^ 2) + 1) - 1 := by
  obtain ⟨Y', rfl⟩ : ∃ Y', Y = Y' + 2 := ⟨Y - 2, by omega⟩
  have h1 : 4 * Y' ≤ U * Y' := Nat.mul_le_mul_right _ hU
  have h2 : (Y' + 2) * (U + 1) + 4 < U * (Y' + 2) ^ 2 := by nlinarith [h1, Nat.zero_le (U * Y' ^ 2)]
  omega

/-- The first Pell index: `k = ψ_P(r + 1)`. -/
theorem k_index {U Y r k h c η ζ τ a J : ℕ} (hU : 4 ≤ U) (hY : 2 ≤ Y) (hr : 1 ≤ r)
    (hJ : J = 2 * r + 1) (hA : 1 < a + 2) (ha : a = Y * (U + 1))
    (hP : 1 < 2 * (U * Y ^ 2) + 1) (hc : c = ψ hA J)
    (E9 : τ * (τ + 1) = (U * Y ^ 2) * (U * Y ^ 2 + 1) * k ^ 2)
    (E10a : c = k * Y + η) (E10b : k = η + ζ) (hζ : 0 < ζ)
    (E11 : k = r + 1 + h * (U * Y)) (hUY : r + 1 < U * Y) :
    k = ψ hP (r + 1) := by
  -- the Pell pair `(2τ + 1, k)` for `P = 2Q + 1`
  obtain ⟨t, hτ, hkt⟩ : ∃ t, 2 * τ + 1 = xn hP t ∧ k = yn hP t := by
    apply eq_pell_of_sq hP
    have e : (2 * (U * Y ^ 2) + 1) ^ 2 - 1 = 4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1)) := by
      have : (2 * (U * Y ^ 2) + 1) ^ 2 = 4 * ((U * Y ^ 2) * (U * Y ^ 2 + 1)) + 1 := by ring
      omega
    rw [e]
    nlinarith [E9]
  have hk0 : 0 < k := by omega
  have ht0 : 0 < t := by
    by_contra h0; push Not at h0
    have : t = 0 := by omega
    rw [this, yn_zero] at hkt; omega
  -- `t ≡ r + 1 (mod U Y)`
  have hmod : k ≡ t [MOD U * Y] := by
    have h1 : yn hP t ≡ t [MOD 2 * (U * Y ^ 2) + 1 - 1] := yn_modEq_a_sub_one hP t
    have h2 : U * Y ∣ 2 * (U * Y ^ 2) + 1 - 1 := ⟨2 * Y, by ring_nf; omega⟩
    rw [← hkt] at h1
    exact Nat.ModEq.of_dvd h2 h1
  have hmod2 : t ≡ r + 1 [MOD U * Y] := by
    have : r + 1 ≡ k [MOD U * Y] := by
      rw [E11]; exact (Nat.modEq_iff_dvd' (by omega)).2 ⟨h, by ring_nf; omega⟩
    exact hmod.symm.trans this.symm
  have hUY0 : 0 < U * Y := by positivity
  -- either `t = r + 1` or `t ≥ r + 1 + UY`
  rcases Nat.lt_or_ge t (U * Y) with hlt | hge
  · have : t = r + 1 := Nat.ModEq.eq_of_lt_of_lt hmod2 hlt hUY
    rw [hkt, this]
  · exfalso
    -- then `k` is huge: `k ≥ (2P−1)^(t−1) ≥ (2P−1)^(2r) > (4A)^(2r) ≥ c`
    have ht : 2 * r + 1 ≤ t := by
      have e1 : t % (U * Y) = (r + 1) % (U * Y) := hmod2
      rw [Nat.mod_eq_of_lt hUY] at e1
      have e2 := Nat.div_add_mod t (U * Y)
      have hq1 : 1 ≤ t / (U * Y) := Nat.div_pos hge hUY0
      have h3 : U * Y ≤ U * Y * (t / (U * Y)) := Nat.le_mul_of_pos_right _ hq1
      omega
    have hk : (2 * (2 * (U * Y ^ 2) + 1) - 1) ^ (2 * r) ≤ k := by
      rw [hkt]
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have h1 := pow_le_ψ_succ hP s
      have h2 : (2 * (2 * (U * Y ^ 2) + 1) - 1) ^ (2 * r) ≤ (2 * (2 * (U * Y ^ 2) + 1) - 1) ^ s :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact h2.trans h1
    have hcb : c ≤ (2 * (a + 2)) ^ (2 * r) := by
      rw [hc, hJ]; exact ψ_succ_le_pow hA (2 * r)
    have h4A := two_A_lt hU hY
    rw [← ha] at h4A
    have hlt2 : (2 * (a + 2)) ^ (2 * r) < (2 * (2 * (U * Y ^ 2) + 1) - 1) ^ (2 * r) := by
      apply Nat.pow_lt_pow_left _ (by omega)
      omega
    have hck : k ≤ c := by
      rw [E10a]
      have : k ≤ k * Y := Nat.le_mul_of_pos_right k (by omega)
      omega
    omega

/-- The lower bound `U^r ≤ Y` from `c/k > ξ` and `c/k < Y + 1`. -/
theorem Y_lower {U Y r k c η ζ a J : ℕ} (hU : 1 ≤ U) (hY : 1 ≤ Y) (hr : 1 ≤ r)
    (hJ : J = 2 * r + 1) (hA : 1 < a + 2) (ha : a = Y * (U + 1))
    (hP : 1 < 2 * (U * Y ^ 2) + 1) (hc : c = ψ hA J) (hk : k = ψ hP (r + 1))
    (E10a : c = k * Y + η) (E10b : k = η + ζ) (hζ : 0 < ζ) :
    U ^ r ≤ Y := by
  -- `c U^r > k (U+1)^(2r)`
  have hcl : (2 * (a + 2) - 1) ^ (2 * r) ≤ c := by
    rw [hc, hJ]; exact pow_le_ψ_succ hA (2 * r)
  have hku : k ≤ (2 * (2 * (U * Y ^ 2) + 1)) ^ r := by
    rw [hk]; exact ψ_succ_le_pow hP r
  have key := lower_key hU hY
  rw [← ha] at key
  have hpow : (2 * (2 * (U * Y ^ 2) + 1) * (U + 1) ^ 2) ^ r < ((2 * (a + 2) - 1) ^ 2 * U) ^ r :=
    Nat.pow_lt_pow_left key (by omega)
  have h1 : k * (U + 1) ^ (2 * r) < c * U ^ r := by
    calc k * (U + 1) ^ (2 * r) ≤ (2 * (2 * (U * Y ^ 2) + 1)) ^ r * (U + 1) ^ (2 * r) :=
          Nat.mul_le_mul_right _ hku
      _ = (2 * (2 * (U * Y ^ 2) + 1) * (U + 1) ^ 2) ^ r := by rw [pow_mul, ← mul_pow]
      _ < ((2 * (a + 2) - 1) ^ 2 * U) ^ r := hpow
      _ = (2 * (a + 2) - 1) ^ (2 * r) * U ^ r := by rw [mul_pow, ← pow_mul]
      _ ≤ c * U ^ r := Nat.mul_le_mul_right _ hcl
  -- `c < k (Y + 1)`
  have h2 : c < k * (Y + 1) := by rw [E10a]; nlinarith
  have hk0 : 0 < k := by omega
  -- so `(Y + 1) U^r > (U+1)^(2r) ≥ U^(2r)`
  have h3 : k * (U + 1) ^ (2 * r) < k * ((Y + 1) * U ^ r) := by
    calc k * (U + 1) ^ (2 * r) < c * U ^ r := h1
      _ < k * (Y + 1) * U ^ r := Nat.mul_lt_mul_of_pos_right h2 (by positivity)
      _ = k * ((Y + 1) * U ^ r) := by ring
  have h4 : (U + 1) ^ (2 * r) < (Y + 1) * U ^ r := Nat.lt_of_mul_lt_mul_left h3
  have h5 : U ^ r * U ^ r ≤ (U + 1) ^ (2 * r) := by
    rw [← pow_add, ← two_mul]; exact Nat.pow_le_pow_left (by omega) _
  have hUr : 0 < U ^ r := by positivity
  by_contra hcon
  push Not at hcon
  have : (Y + 1) * U ^ r ≤ U ^ r * U ^ r := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The main parameter shift `a = Y(U+1)` exceeds `U^(r+1)` once `U^r ≤ Y`. -/
theorem a_gt {U Y r a : ℕ} (hU : 1 ≤ U) (ha : a = Y * (U + 1)) (hYr : U ^ r ≤ Y) :
    U ^ (r + 1) < a := by
  rw [ha, pow_succ]
  have h1 : U ^ r * U < U ^ r * (U + 1) := by
    have : 0 < U ^ r := by positivity
    nlinarith
  calc U ^ r * U < U ^ r * (U + 1) := h1
    _ ≤ Y * (U + 1) := Nat.mul_le_mul_right _ hYr

/-- The lower estimate `k (U+1)^(2r) < c U^r` (the integer form of `ξ < c/k`). -/
theorem lower_estimate {U Y r k c a J : ℕ} (hU : 1 ≤ U) (hY : 1 ≤ Y) (hr : 1 ≤ r)
    (hJ : J = 2 * r + 1) (hA : 1 < a + 2) (ha : a = Y * (U + 1))
    (hP : 1 < 2 * (U * Y ^ 2) + 1) (hc : c = ψ hA J) (hk : k = ψ hP (r + 1)) :
    k * (U + 1) ^ (2 * r) < c * U ^ r := by
  have hcl : (2 * (a + 2) - 1) ^ (2 * r) ≤ c := by
    rw [hc, hJ]; exact pow_le_ψ_succ hA (2 * r)
  have hku : k ≤ (2 * (2 * (U * Y ^ 2) + 1)) ^ r := by
    rw [hk]; exact ψ_succ_le_pow hP r
  have key := lower_key hU hY
  rw [← ha] at key
  have hpow : (2 * (2 * (U * Y ^ 2) + 1) * (U + 1) ^ 2) ^ r < ((2 * (a + 2) - 1) ^ 2 * U) ^ r :=
    Nat.pow_lt_pow_left key (by omega)
  calc k * (U + 1) ^ (2 * r) ≤ (2 * (2 * (U * Y ^ 2) + 1)) ^ r * (U + 1) ^ (2 * r) :=
        Nat.mul_le_mul_right _ hku
    _ = (2 * (2 * (U * Y ^ 2) + 1) * (U + 1) ^ 2) ^ r := by rw [pow_mul, ← mul_pow]
    _ < ((2 * (a + 2) - 1) ^ 2 * U) ^ r := hpow
    _ = (2 * (a + 2) - 1) ^ (2 * r) * U ^ r := by rw [mul_pow, ← pow_mul]
    _ ≤ c * U ^ r := Nat.mul_le_mul_right _ hcl

/-! ### The real half -/

/-- `(2A)² U ⋅ Y(U+1) ≤ (2P − 1)(U+1)² ⋅ (Y(U+1) + 9)` for `Y(U+1) ≥ 16`. -/
theorem upper_key {U Y : ℕ} (hU : 1 ≤ U) (hY : 1 ≤ Y) (h16 : 16 ≤ Y * (U + 1)) :
    (2 * (Y * (U + 1) + 2)) ^ 2 * U * (Y * (U + 1)) ≤
      (2 * (2 * (U * Y ^ 2) + 1) - 1) * (U + 1) ^ 2 * (Y * (U + 1) + 9) := by
  have e : 2 * (2 * (U * Y ^ 2) + 1) - 1 = 4 * (U * Y ^ 2) + 1 := by omega
  rw [e]
  have h1 : U * Y * 16 ≤ U * Y * (Y * (U + 1)) := Nat.mul_le_mul_left _ h16
  nlinarith [h1]

/-- `(1 + ε)^r ≤ 1 + 2rε` for `0 ≤ ε` with `rε ≤ 1/2`. -/
theorem one_add_pow_le {ε : ℝ} (r : ℕ) (hε : 0 ≤ ε) (hrε : (r : ℝ) * ε ≤ 1 / 2) :
    (1 + ε) ^ r ≤ 1 + 2 * (r * ε) := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast h
  have hε1 : ε ≤ 1 := by nlinarith
  have h5 : (1 + ε) ^ r * (1 - ε) ^ r ≤ 1 := by
    rw [← mul_pow]
    have : (1 + ε) * (1 - ε) = 1 - ε ^ 2 := by ring
    rw [this]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h2 : 1 - r * ε ≤ (1 - ε) ^ r := Jones1982.ineq_2_17_a hε1 r
  have h3 : (1 - r * ε)⁻¹ ≤ 1 + 2 * (r * ε) := Jones1982.ineq_2_17_b (by positivity) hrε
  have hpos : 0 < 1 - r * ε := by linarith
  have hpos' : 0 < (1 - ε) ^ r := lt_of_lt_of_le hpos h2
  have h4 : (1 + ε) ^ r ≤ 1 / (1 - ε) ^ r := by
    rw [le_div_iff₀ hpos']; linarith [h5]
  have h6 : 1 / (1 - ε) ^ r ≤ 1 / (1 - r * ε) := one_div_le_one_div_of_le hpos h2
  calc (1 + ε) ^ r ≤ 1 / (1 - ε) ^ r := h4
    _ ≤ 1 / (1 - r * ε) := h6
    _ = (1 - r * ε)⁻¹ := one_div _
    _ ≤ 1 + 2 * (r * ε) := h3

/-- The upper estimate `c/k < ξ + 1/2` once `72 r < U + 1`, `U^r ≤ Y` and `16 ≤ Y(U+1)`. -/
theorem upper_estimate' {U Y r k c a J : ℕ} (hU : 1 ≤ U) (hY : 1 ≤ Y) (hr : 1 ≤ r)
    (hJ : J = 2 * r + 1) (hA : 1 < a + 2) (ha : a = Y * (U + 1))
    (hP : 1 < 2 * (U * Y ^ 2) + 1) (hc : c = ψ hA J) (hk : k = ψ hP (r + 1))
    (hξY' : ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r < Y + 1)
    (h72 : 72 * r < U + 1) (hYr : U ^ r ≤ Y) (h16 : 16 ≤ Y * (U + 1)) :
    (c : ℝ) / k < ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r + 1 / 2 := by
  have hk0 : 0 < k := by
    rw [hk]; exact lt_of_lt_of_le (Nat.succ_pos r) (Pell.yn_ge_n hP (r + 1))
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hUR : (0 : ℝ) < (U : ℝ) ^ r := by positivity
  have hU1 : (0 : ℝ) < (U : ℝ) + 1 := by positivity
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hYU : (0 : ℝ) < (Y : ℝ) * (U + 1) := by positivity
  have haR : (a : ℝ) = Y * (U + 1) := by rw [ha]; push_cast; ring
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℝ, ξ = ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r := ⟨_, rfl⟩
  have hξdef : ((U : ℝ) + 1) ^ (2 * r) = ξ * (U : ℝ) ^ r := by rw [hξ]; field_simp
  rw [← hξ]
  -- growth bounds
  have hcb : (c : ℝ) ≤ (2 * ((a : ℝ) + 2)) ^ (2 * r) := by
    have := ψ_succ_le_pow hA (2 * r)
    rw [← hJ, ← hc] at this
    exact_mod_cast this
  have hkb : ((2 * (2 * (U * Y ^ 2) + 1) - 1 : ℕ) : ℝ) ^ r ≤ k := by
    have := pow_le_ψ_succ hP r
    rw [← hk] at this
    exact_mod_cast this
  -- `Z = (2A)² U ≤ X (1 + ε)`, `X = (2P−1)(U+1)²`, `ε = 9/(Y(U+1))`
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ((2 * (2 * (U * Y ^ 2) + 1) - 1 : ℕ) : ℝ) * ((U : ℝ) + 1) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = (2 * ((a : ℝ) + 2)) ^ 2 * U := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 9 / ((Y : ℝ) * (U + 1)) := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hXpos : 0 < X := by
    rw [hX]
    have : (1 : ℕ) ≤ 2 * (2 * (U * Y ^ 2) + 1) - 1 := by omega
    have : (1 : ℝ) ≤ ((2 * (2 * (U * Y ^ 2) + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast this
    positivity
  have hZX : Z ≤ X * (1 + ε) := by
    have key := upper_key hU hY h16
    have keyR : Z * ((Y : ℝ) * (U + 1)) ≤ X * ((Y : ℝ) * (U + 1) + 9) := by
      rw [hZ, hX, haR]
      exact_mod_cast key
    have e : X * (1 + ε) = X * ((Y : ℝ) * (U + 1) + 9) / ((Y : ℝ) * (U + 1)) := by
      rw [hε]; field_simp
    rw [e, le_div_iff₀ hYU]
    exact keyR
  -- `c U^r ≤ Z^r` and `X^r ≤ k (U+1)^(2r)`
  have hcZ : (c : ℝ) * (U : ℝ) ^ r ≤ Z ^ r := by
    have e : Z ^ r = (2 * ((a : ℝ) + 2)) ^ (2 * r) * (U : ℝ) ^ r := by
      rw [hZ, mul_pow, ← pow_mul]
    rw [e]; exact mul_le_mul_of_nonneg_right hcb hUR.le
  have hXk : X ^ r ≤ (k : ℝ) * ((U : ℝ) + 1) ^ (2 * r) := by
    have e : X ^ r = ((2 * (2 * (U * Y ^ 2) + 1) - 1 : ℕ) : ℝ) ^ r * ((U : ℝ) + 1) ^ (2 * r) := by
      rw [hX, mul_pow, ← pow_mul]
    rw [e]; exact mul_le_mul_of_nonneg_right hkb (by positivity)
  -- `(1+ε)^r ≤ 1 + 2rε`
  have h72R : (72 : ℝ) * r < U + 1 := by exact_mod_cast h72
  have hrε : (r : ℝ) * ε ≤ 1 / 2 := by
    rw [hε, mul_div_assoc', div_le_iff₀ hYU]
    nlinarith
  have hpow := one_add_pow_le r hε0 hrε
  -- `c U^r ≤ k ξ U^r (1 + 2rε)`, hence `c ≤ k ξ (1 + 2rε)`
  have h1 : (c : ℝ) * (U : ℝ) ^ r ≤ (k : ℝ) * ξ * (1 + 2 * (r * ε)) * (U : ℝ) ^ r := by
    calc (c : ℝ) * (U : ℝ) ^ r ≤ Z ^ r := hcZ
      _ ≤ (X * (1 + ε)) ^ r := pow_le_pow_left₀ (by rw [hZ]; positivity) hZX r
      _ = X ^ r * (1 + ε) ^ r := mul_pow _ _ _
      _ ≤ (k : ℝ) * ((U : ℝ) + 1) ^ (2 * r) * (1 + 2 * (r * ε)) := by
          apply mul_le_mul hXk hpow (by positivity) (by positivity)
      _ = (k : ℝ) * ξ * (1 + 2 * (r * ε)) * (U : ℝ) ^ r := by rw [hξdef]; ring
  have h1' : (c : ℝ) ≤ (k : ℝ) * ξ * (1 + 2 * (r * ε)) := le_of_mul_le_mul_right h1 hUR
  have hξY : ξ < Y + 1 := by rw [hξ]; exact hξY'
  -- `ξ ⋅ 2rε < 1/2`
  have hsmall : ξ * (2 * (r * ε)) < 1 / 2 := by
    have hε' : (Y + 1 : ℝ) * (2 * (r * ε)) < 1 / 2 := by
      rw [hε]
      have e : ((Y : ℝ) + 1) * (2 * (r * (9 / ((Y : ℝ) * (U + 1))))) =
          18 * r * (Y + 1) / (Y * (U + 1)) := by field_simp; ring
      rw [e, div_lt_iff₀ hYU]
      nlinarith
    have hξ0 : 0 ≤ ξ := by rw [hξ]; positivity
    calc ξ * (2 * (r * ε)) ≤ (Y + 1 : ℝ) * (2 * (r * ε)) :=
          mul_le_mul_of_nonneg_right hξY.le (by positivity)
      _ < 1 / 2 := hε'
  -- conclude
  rw [div_lt_iff₀ hkR]
  calc (c : ℝ) ≤ k * ξ * (1 + 2 * (r * ε)) := h1'
    _ = k * ξ + k * (ξ * (2 * (r * ε))) := by ring
    _ < k * ξ + k * (1 / 2) := by
        have := mul_lt_mul_of_pos_left hsmall hkR
        linarith
    _ = (ξ + 1 / 2) * k := by ring

theorem upper_estimate {U Y r k c η ζ a J : ℕ} (hU : 1 ≤ U) (hY : 1 ≤ Y) (hr : 1 ≤ r)
    (hJ : J = 2 * r + 1) (hA : 1 < a + 2) (ha : a = Y * (U + 1))
    (hP : 1 < 2 * (U * Y ^ 2) + 1) (hc : c = ψ hA J) (hk : k = ψ hP (r + 1))
    (E10a : c = k * Y + η) (E10b : k = η + ζ) (hζ : 0 < ζ)
    (h72 : 72 * r < U + 1) (hYr : U ^ r ≤ Y) (h16 : 16 ≤ Y * (U + 1)) :
    (c : ℝ) / k < ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r + 1 / 2 := by
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hUR : (0 : ℝ) < (U : ℝ) ^ r := by positivity
  have hξY' : ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r < Y + 1 := by
    have hlow := lower_estimate hU hY hr hJ hA ha hP hc hk
    have hlowR : (k : ℝ) * ((U : ℝ) + 1) ^ (2 * r) < c * (U : ℝ) ^ r := by exact_mod_cast hlow
    have h3 : (c : ℝ) < k * (Y + 1) := by
      have : c < k * (Y + 1) := by rw [E10a]; nlinarith
      exact_mod_cast this
    rw [div_lt_iff₀ hUR]
    have h4 : (k : ℝ) * ((U : ℝ) + 1) ^ (2 * r) < k * ((Y + 1) * (U : ℝ) ^ r) := by
      calc (k : ℝ) * ((U : ℝ) + 1) ^ (2 * r) < c * (U : ℝ) ^ r := hlowR
        _ ≤ k * (Y + 1) * (U : ℝ) ^ r := mul_le_mul_of_nonneg_right h3.le hUR.le
        _ = k * ((Y + 1) * (U : ℝ) ^ r) := by ring
    exact lt_of_mul_lt_mul_left h4 hkR.le
  exact upper_estimate' hU hY hr hJ hA ha hP hc hk hξY' h72 hYr h16

/-! ### The exact binomial tail for base two (§5 of `BASE_TWO_PELL_90_PROOF.md`)

With `U = 2^(2r+1) = 2·4^r`, the crude tail bound `Σ_{m<r} C(2r,m)/U^(r−m) < 2^(2r)/U` of
Lemma 2.24 only gives `< 1/2`; the symmetry `2 Σ_{m<r} C(2r,m) + C(2r,r) = 4^r` sharpens it
to `≤ (4^r − C(2r,r))/(2U) < 1/4`. -/

/-- `2 Σ_{m<R} C(2R,m) + C(2R,R) = 2^(2R)` (symmetry of the binomial coefficients). -/
theorem two_mul_sum_choose_add (R : ℕ) :
    2 * (∑ m ∈ Finset.range R, (2 * R).choose m) + (2 * R).choose R = 2 ^ (2 * R) := by
  have h := Nat.sum_range_choose (2 * R)
  have hsplit : ∑ m ∈ Finset.range (2 * R + 1), (2 * R).choose m =
      ∑ m ∈ Finset.range (R + 1), (2 * R).choose m
        + ∑ m ∈ Finset.Ico (R + 1) (2 * R + 1), (2 * R).choose m :=
    (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  have hrefl : ∑ m ∈ Finset.Ico (R + 1) (2 * R + 1), (2 * R).choose m =
      ∑ m ∈ Finset.range R, (2 * R).choose m := by
    have h1 : ∑ m ∈ Finset.Ico (R + 1) (2 * R + 1), (2 * R).choose m =
        ∑ m ∈ Finset.Ico (R + 1) (2 * R + 1), (2 * R).choose (2 * R - m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_Ico] at hm
      rw [Nat.choose_symm (by omega)]
    rw [h1, Finset.sum_Ico_reflect _ _ (by omega : 2 * R + 1 ≤ 2 * R + 1),
      show 2 * R + 1 - (2 * R + 1) = 0 by omega, show 2 * R + 1 - (R + 1) = R by omega,
      Finset.range_eq_Ico]
  rw [hsplit, hrefl, Finset.sum_range_succ] at h
  omega

/-- Lemma 2.24 with the exact tail bound: for `R ≥ 1` and `2^(2R+1) ≤ U`,
`(U+1)^(2R) = Q U^R + v` with `4 v < U^R` and `Q = C(2R,R) + w U`. -/
theorem binomial_floor_two {R U : ℕ} (hR : 1 ≤ R) (hU : 2 ^ (2 * R + 1) ≤ U) :
    ∃ Q v w : ℕ, (U + 1) ^ (2 * R) = Q * U ^ R + v ∧ 4 * v < U ^ R ∧
      Q = (2 * R).choose R + w * U := by
  have hU1 : 1 ≤ U := le_trans Nat.one_le_two_pow hU
  have h := add_pow U 1 (2 * R)
  simp only [one_pow, mul_one, Nat.cast_id] at h
  have hsplit : ∑ m ∈ Finset.range (2 * R + 1), U ^ m * (2 * R).choose m =
      ∑ m ∈ Finset.range R, U ^ m * (2 * R).choose m + U ^ R * (2 * R).choose R
        + ∑ m ∈ Finset.Ico (R + 1) (2 * R + 1), U ^ m * (2 * R).choose m := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le R) (by omega : R ≤ 2 * R + 1),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : R < 2 * R + 1)]
    ring
  have hdvd : U ^ (R + 1) ∣ ∑ m ∈ Finset.Ico (R + 1) (2 * R + 1), U ^ m * (2 * R).choose m := by
    apply Finset.dvd_sum
    intro m hm
    simp only [Finset.mem_Ico] at hm
    exact Dvd.dvd.mul_right (pow_dvd_pow U hm.1) _
  obtain ⟨w, hw⟩ := hdvd
  refine ⟨(2 * R).choose R + w * U, ∑ m ∈ Finset.range R, U ^ m * (2 * R).choose m, w, ?_, ?_,
    rfl⟩
  · rw [h, hsplit, hw]; ring
  · have hle : ∑ m ∈ Finset.range R, U ^ m * (2 * R).choose m ≤
        U ^ (R - 1) * ∑ m ∈ Finset.range R, (2 * R).choose m := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      simp only [Finset.mem_range] at hm
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hU1 (by omega))
    have hsym := two_mul_sum_choose_add R
    have hpos : 0 < (2 * R).choose R := Nat.choose_pos (by omega)
    have hUR : U ^ R = U ^ (R - 1) * U := by
      rw [← pow_succ, Nat.sub_add_cancel hR]
    have hUpos : 0 < U ^ (R - 1) := Nat.pow_pos hU1
    calc 4 * ∑ m ∈ Finset.range R, U ^ m * (2 * R).choose m
        ≤ 4 * (U ^ (R - 1) * ∑ m ∈ Finset.range R, (2 * R).choose m) :=
          Nat.mul_le_mul_left _ hle
      _ = U ^ (R - 1) * (2 * (2 * ∑ m ∈ Finset.range R, (2 * R).choose m)) := by ring
      _ < U ^ (R - 1) * (2 * 2 ^ (2 * R)) := by
          apply Nat.mul_lt_mul_of_pos_left _ hUpos
          omega
      _ = U ^ (R - 1) * 2 ^ (2 * R + 1) := by rw [pow_succ]; ring
      _ ≤ U ^ (R - 1) * U := Nat.mul_le_mul_left _ hU
      _ = U ^ R := hUR.symm

/-- `Y = ⌊(U+1)^(2r)/U^r⌋`, with the base-two size `2^(2r+1) ≤ U`. -/
theorem Y_eq_floor {U Y r k c η ζ : ℕ} (hr : 1 ≤ r) (hU4 : 2 ^ (2 * r + 1) ≤ U)
    (hk0 : 0 < k) (hη : 0 < η) (E10a : c = k * Y + η) (E10b : k = η + ζ) (hζ : 0 < ζ)
    (hlow : k * (U + 1) ^ (2 * r) < c * U ^ r)
    (hup : (c : ℝ) / k < ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r + 1 / 2) :
    ∃ w : ℕ, Y = (2 * r).choose r + w * U := by
  obtain ⟨F, v, w, hsplit, hv, hF⟩ := binomial_floor_two hr hU4
  refine ⟨w, ?_⟩
  rw [← hF]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hU0 : 0 < U := lt_of_lt_of_le (Nat.two_pow_pos _) hU4
  have hUR : (0 : ℝ) < (U : ℝ) ^ r := by positivity
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℝ, ξ = ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (c : ℝ) / k := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (v : ℝ) / (U : ℝ) ^ r := ⟨_, rfl⟩
  rw [← hξ, ← hρ] at hup
  -- `ξ = F + δ` with `0 ≤ δ < 1/4`
  have hξF : ξ = F + δ := by
    rw [hξ, hδ]
    have : ((U : ℝ) + 1) ^ (2 * r) = F * (U : ℝ) ^ r + v := by exact_mod_cast hsplit
    rw [this]; field_simp
  have hδlt : δ < 1 / 4 := by
    rw [hδ, div_lt_iff₀ hUR]
    have : (4 * v : ℝ) < (U : ℝ) ^ r := by exact_mod_cast hv
    linarith
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  -- `Y < ρ < Y + 1`
  have hY1 : (Y : ℝ) < ρ := by
    rw [hρ, lt_div_iff₀ hkR]
    have : Y * k < c := by rw [E10a, mul_comm]; omega
    exact_mod_cast this
  have hY2 : ρ < Y + 1 := by
    rw [hρ, div_lt_iff₀ hkR]
    have : c < (Y + 1) * k := by rw [E10a]; nlinarith
    exact_mod_cast this
  -- `ξ < ρ`
  have hξρ : ξ < ρ := by
    have e1 : ξ * (U : ℝ) ^ r = ((U : ℝ) + 1) ^ (2 * r) := by rw [hξ]; field_simp
    have hlowR : (k : ℝ) * ((U : ℝ) + 1) ^ (2 * r) < c * (U : ℝ) ^ r := by exact_mod_cast hlow
    rw [← e1] at hlowR
    have h : ξ * k * (U : ℝ) ^ r < c * (U : ℝ) ^ r := by linarith [hlowR]
    have h2 : ξ * k < c := lt_of_mul_lt_mul_right h hUR.le
    rw [hρ, lt_div_iff₀ hkR]; exact h2
  -- `F ≤ Y` and `Y ≤ F`
  have h1 : (F : ℝ) < Y + 1 := by linarith
  have h2 : (Y : ℝ) < F + 1 := by linarith
  have h1' : F < Y + 1 := by exact_mod_cast h1
  have h2' : Y < F + 1 := by exact_mod_cast h2
  omega

/-- The central-binomial divisibility `n² ∣ C(2r, r)` from `Y = C(2r,r) + wU`, `n² ∣ U`,
`n² ∣ Y`. -/
theorem central_dvd {n U Y r w : ℕ} (hU : n ^ 2 ∣ U) (hY : n ^ 2 ∣ Y)
    (h : Y = (2 * r).choose r + w * U) : n ^ 2 ∣ (2 * r).choose r := by
  have h1 : n ^ 2 ∣ w * U := Dvd.dvd.mul_left hU w
  have h2 : (2 * r).choose r = Y - w * U := by omega
  rw [h2]; exact Nat.dvd_sub hY h1

end Ratio90

end Jones1980
