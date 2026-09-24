import Diophantine.Paper1980.GridCompiled100

/-!
# The raw counter history

`EXPLORATION_PARITY_ALIGNED_RAW_COUNTERS.md`, §§2–3, as used by
`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §5.  The time equation of the counter system is

    W (A + δ) = A − I,   W = R³,   A = A₀ + A₁,   δ = K⁺ − K⁻,   I = 4x.

Halving it and reading both sides in base `R` block by block gives the whole counter
history: with `a_b` the `b`-th block of the halved track word and `ε_b = ±1` the `b`-th sign,
the coefficient of `R^b` in `(a − 2x) − R³(a + κ⁺ − κ⁻)` is

    a_b − [b = 0]·2x − [b ≥ 3]·(a_{b−3} + ε_{b−3}),

every such coefficient is smaller than `R` in absolute value, and a signed base-`R` numeral
with small digits vanishes only when every digit does (`signed_digits_zero`).  So the three
residue chains start at `[2x, 0, 0]`, move by `ε` at every step, and end at zero.

The guard pairs bound the blocks: halved, `t/2 = κ·(D/2)` with `6κ = R − 3`, and each track
is digitwise below `t/2`, so every block is at most `2κ < R/3`, and a block whose zero field
row is empty holds zero.  That last fact is the source-zero test.
-/

namespace Jones1980

open Ternary Finset

/-! ### General lemmas -/

/-- **A signed base-`R` numeral with small digits vanishes only digitwise.** -/
theorem signed_digits_zero {R : ℤ} (hR : 0 < R) :
    ∀ (N : ℕ) (cf : ℕ → ℤ), (∀ b, |cf b| < R) → ∑ b ∈ range N, cf b * R ^ b = 0 →
      ∀ b, b < N → cf b = 0 := by
  intro N
  induction N with
  | zero => intro cf _ _ b hb; omega
  | succ N ih =>
    intro cf hc hsum b hb
    rw [Finset.sum_range_succ'] at hsum
    have hshift : ∑ i ∈ range N, cf (i + 1) * R ^ (i + 1)
        = R * ∑ i ∈ range N, cf (i + 1) * R ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    obtain ⟨S, hS⟩ : ∃ S, S = ∑ i ∈ range N, cf (i + 1) * R ^ i := ⟨_, rfl⟩
    rw [hshift, ← hS, pow_zero, mul_one] at hsum
    have h0 : cf 0 = 0 := by
      obtain ⟨k, hk⟩ : R ∣ cf 0 := ⟨-S, by linarith⟩
      have hb0 := hc 0
      rw [hk, abs_mul, abs_of_pos hR] at hb0
      have h1 : R * |k| < R * 1 := by linarith
      have h2 : |k| < 1 := lt_of_mul_lt_mul_left h1 (le_of_lt hR)
      have h3 : k = 0 := by rw [abs_lt] at h2; omega
      rw [hk, h3, mul_zero]
    have hS0 : S = 0 := by
      rw [h0] at hsum
      have hRS : R * S = 0 := by linarith
      rcases mul_eq_zero.1 hRS with h | h
      · linarith
      · exact h
    rcases b with _ | b
    · exact h0
    · have hrec := ih (fun i => cf (i + 1)) (fun i => hc (i + 1)) (by rw [← hS0, hS]) b (by omega)
      exact hrec

/-- Rows add when each pair of rows fits inside a row. -/
theorem row_add_small {X Y m u : ℕ} (hX : X < 3 ^ (m * u)) (hY : Y < 3 ^ (m * u))
    (hsmall : ∀ b, row X m b + row Y m b < 3 ^ m) {b : ℕ} (hb : b < u) :
    row (X + Y) m b = row X m b + row Y m b := by
  have hx := sum_rows u hX
  have hy := sum_rows u hY
  have hsum : X + Y = rowsum (fun k => row X m k + row Y m k) m u := by
    unfold rowsum
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsum]
  exact row_rowsum hsmall u b hb

/-- Two Boolean words add rowwise. -/
theorem row_add_of_bool {X Y m b : ℕ} (hX : Bool3 X) (hY : Bool3 Y) :
    row (X + Y) m b = row X m b + row Y m b := by
  unfold row
  rw [Ternary.add_div_of_bool hX hY,
    Ternary.add_mod_of_bool (hX.div_pow _) (hY.div_pow _)]

/-- The grid width minus three is a multiple of six. -/
theorem six_dvd_pow_sub_three : ∀ k : ℕ, 6 ∣ 3 ^ (k + 1) - 3
  | 0 => by norm_num
  | k + 1 => by
    have h := six_dvd_pow_sub_three k
    have hge : 3 ≤ 3 ^ (k + 1) := by
      have := Nat.one_le_pow k 3 (by norm_num)
      rw [pow_succ]
      omega
    rw [pow_succ]
    omega

/-- A word below the height, read as an integer numeral in its rows. -/
theorem sum_rows_int {X m N : ℕ} (hX : X < 3 ^ (m * N)) :
    (X : ℤ) = ∑ b ∈ range N, (row X m b : ℤ) * ((3 : ℤ) ^ m) ^ b := by
  have h := sum_rows N hX
  have h2 : ((X : ℕ) : ℤ) = ((∑ b ∈ range N, row X m b * 3 ^ (m * b) : ℕ) : ℤ) :=
    congrArg _ h
  rw [h2]
  push_cast
  exact Finset.sum_congr rfl fun b _ => by rw [← pow_mul]

/-! ### The counter history of the counter certificate -/

section History

variable {C : ROM100}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  {e m u dm pK amin amax : ℕ}
  (hOk : C.Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hG : Geometry100 H R q e m u)

include hOk hP hS hG

set_option maxHeartbeats 4000000 in
/-- **The counter history.**  Halving the track, sign and zero fields, the `b`-th block of
the halved track word is at most `(R − 3)/3` and vanishes wherever the zero field's row is
empty; the three residue chains start at `[2x, 0, 0]`; and each block equals the block three
places earlier plus that block's sign, up to three places past the top, where the chains
end at zero. -/
theorem counter_history_rom100 (hSid : C.Sidon dm pK) (hLay : C.Layout dm pK amin amax)
    (hDq : 2 * q ≤ R * D) :
    ∃ a0 a1 kp km dd, A0 = 2 * a0 ∧ A1 = 2 * a1 ∧ Kp = 2 * kp ∧ Km = 2 * km ∧ D = 2 * dd ∧
      (∀ b, b < u → row kp m b + row km m b = 1) ∧
      (∀ b, row (a0 + a1) m b ≤ (R - 3) / 3 * row dd m b) ∧
      row (a0 + a1) m 0 = 2 * x ∧ row (a0 + a1) m 1 = 0 ∧ row (a0 + a1) m 2 = 0 ∧
      (∀ b, 3 ≤ b → b < u + 3 →
        (row (a0 + a1) m b : ℤ) + row km m (b - 3)
          = row (a0 + a1) m (b - 3) + row kp m (b - 3)) := by
  -- ## the decoded fields
  have hdm := marker_lt_width hOk hP hS hG hSid
  have hN := nonneg_full100 hOk hP hS hG hSid (le_of_lt hdm) (state_lt_width hOk hP hS hG hSid)
    (state_small hOk hP hS hG hSid) hOk.I_pos (code_small hOk hP hS hG hSid)
    (route_residue100 hOk hP hS hG hSid) (exponent_layout100 hOk hP hS hG hSid hLay) hDq
  obtain ⟨⟨kp, hkp, -, hKp⟩, ⟨km, hkm, -, hKm⟩, ⟨ddb, hddb, -, hHD⟩, ⟨dd, hdd, -, hD⟩,
    ⟨g0, hg0, -, hTA0⟩, ⟨a0, ha0, -, hA0⟩, ⟨g1, hg1, -, hTA1⟩, ⟨a1, ha1, -, hA1⟩,
    -, -, -, -⟩ := decode_compiled100 hOk hP hS hG hSid
      (exponent_layout100 hOk hP hS hG hSid hLay) hDq
  refine ⟨a0, a1, kp, km, dd, hA0, hA1, hKp, hKm, hD, ?_⟩
  -- ## geometry
  have hR := hG.hR
  have hm1 := hG.hm
  have hu3 := hG.hu
  have hHh := hG.hH
  have h13m : 1 < 3 ^ m := by
    have : (3 : ℕ) ^ 1 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
    omega
  have hRbig := R_big hOk hP hS
  have hR3 : 3 ≤ R := by omega
  -- ## the halved pairs
  have hE3 := hS.E3
  have hsumK : kp + km = 1 * heads m u := by omega
  have hDle := hN.D_le
  have hsumD : dd + ddb = 1 * heads m u := by omega
  have hA0le := hN.A0_le
  have hA1le := hN.A1_le
  have htt0 : t = 2 * (a0 + g0) := by omega
  have htt1 : t = 2 * (a1 + g1) := by omega
  have hheads := heads_lt m u hm1
  have hddB : dd < 3 ^ (m * u) := by omega
  have hkpB : kp < 3 ^ (m * u) := by omega
  have hkmB : km < 3 ^ (m * u) := by omega
  -- ## the gap is `κ` times the zero field
  obtain ⟨κ, hκ⟩ : ∃ κ, R - 3 = 6 * κ := by
    obtain ⟨k', hk'⟩ : ∃ k', m = k' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨κ, hκ⟩ := six_dvd_pow_sub_three k'
    exact ⟨κ, by rw [hR, hk']; exact hκ⟩
  have hE5 := hS.E5
  have htt : a0 + g0 = κ * dd := by
    have h1 : 6 * t + 3 * D = D * R := hE5
    rw [htt0, hD] at h1
    have h2 : dd * R = dd * (R - 3) + 3 * dd := by
      have hRe : R = (R - 3) + 3 := by omega
      conv_lhs => rw [hRe]
      ring
    have h3 : dd * (R - 3) = 6 * (κ * dd) := by rw [hκ]; ring
    have h4 : 2 * dd * R = 2 * (dd * R) := by ring
    omega
  have htt' : a1 + g1 = κ * dd := by omega
  -- ## rows
  have hdrow : ∀ b, row dd m b ≤ 1 := fun b => by
    rcases Nat.lt_or_ge b u with hb | hb
    · exact state_row_le hdd hddb h13m hb hsumD
    · rw [row_eq_zero_of_ge hddB hb]; omega
  have hprow : ∀ b, row kp m b ≤ 1 := fun b => by
    rcases Nat.lt_or_ge b u with hb | hb
    · exact state_row_le hkp hkm h13m hb hsumK
    · rw [row_eq_zero_of_ge hkpB hb]; omega
  have hmrow : ∀ b, row km m b ≤ 1 := fun b => by
    rcases Nat.lt_or_ge b u with hb | hb
    · have hsumK' : km + kp = 1 * heads m u := by omega
      exact state_row_le hkm hkp h13m hb hsumK'
    · rw [row_eq_zero_of_ge hkmB hb]; omega
  have hκR : κ < 3 ^ m := by omega
  have hκfit : ∀ b, κ * row dd m b < 3 ^ m := fun b => by
    have h1 : κ * row dd m b ≤ κ * 1 := Nat.mul_le_mul_left _ (hdrow b)
    omega
  have httrow : ∀ b, row (κ * dd) m b = κ * row dd m b := fun b => by
    rcases Nat.lt_or_ge b u with hb | hb
    · exact row_mul hκfit hddB hb
    · rw [row_eq_zero_of_ge (mul_lt_of_rows hκfit hddB) hb, row_eq_zero_of_ge hddB hb, mul_zero]
  have ha0row : ∀ b, row a0 m b ≤ κ * row dd m b := fun b => by
    have hsplit := row_add_of_bool (m := m) (b := b) ha0 hg0
    rw [htt, httrow b] at hsplit
    omega
  have ha1row : ∀ b, row a1 m b ≤ κ * row dd m b := fun b => by
    have hsplit := row_add_of_bool (m := m) (b := b) ha1 hg1
    rw [htt', httrow b] at hsplit
    omega
  have hκdd : κ * dd < 3 ^ (m * u) := mul_lt_of_rows hκfit hddB
  have ha0B : a0 < 3 ^ (m * u) := by omega
  have ha1B : a1 < 3 ^ (m * u) := by omega
  have hsmall : ∀ b, row a0 m b + row a1 m b < 3 ^ m := fun b => by
    have h1 := ha0row b
    have h2 := ha1row b
    have h3 : κ * row dd m b ≤ κ * 1 := Nat.mul_le_mul_left _ (hdrow b)
    omega
  have hAB : a0 + a1 < 3 ^ (m * u) := by
    have hsum : a0 + a1 = rowsum (fun k => row a0 m k + row a1 m k) m u := by
      have hx := sum_rows u ha0B
      have hy := sum_rows u ha1B
      unfold rowsum
      conv_lhs => rw [hx, hy]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum]
    exact rowsum_lt hsmall u
  have hArow : ∀ b, row (a0 + a1) m b ≤ 2 * κ := fun b => by
    rcases Nat.lt_or_ge b u with hb | hb
    · rw [row_add_small ha0B ha1B hsmall hb]
      have h1 := ha0row b
      have h2 := ha1row b
      have h3 : κ * row dd m b ≤ κ * 1 := Nat.mul_le_mul_left _ (hdrow b)
      omega
    · rw [row_eq_zero_of_ge hAB hb]; omega
  refine ⟨fun b hb => state_row hkp hkm h13m hb hsumK, fun b => ?_, ?_⟩
  · have hdiv3 : (R - 3) / 3 = 2 * κ := by omega
    rw [hdiv3]
    rcases Nat.lt_or_ge b u with hb | hb
    · rw [row_add_small ha0B ha1B hsmall hb]
      have h1 := ha0row b
      have h2 := ha1row b
      have h3 : 2 * κ * row dd m b = κ * row dd m b + κ * row dd m b := by ring
      omega
    · rw [row_eq_zero_of_ge hAB hb]; exact Nat.zero_le _
  -- ## the halved time equation, as a signed numeral
  have hE6 := hS.E6
  have hE19 := hS.E19
  have hE7 := hS.E7
  have hα := hP.α
  have htime : R ^ 3 * (a0 + a1 + kp) + 2 * x = a0 + a1 + R ^ 3 * km := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    have h6 : W * (A0 + A1 + Kp) + 4 * x = A0 + A1 + W * Km := hE6
    rw [hE19, hA0, hA1, hKp, hKm] at h6
    calc 2 * (R ^ 3 * (a0 + a1 + kp) + 2 * x)
        = R ^ 3 * (2 * a0 + 2 * a1 + 2 * kp) + 4 * x := by ring
      _ = 2 * a0 + 2 * a1 + R ^ 3 * (2 * km) := h6
      _ = 2 * (a0 + a1 + R ^ 3 * km) := by ring
  obtain ⟨cf, hcf⟩ : ∃ cf : ℕ → ℤ, cf = fun b =>
      (row (a0 + a1) m b : ℤ) - (if b = 0 then (2 * x : ℤ) else 0)
        - (if 3 ≤ b then ((row (a0 + a1) m (b - 3) : ℤ) + row kp m (b - 3) - row km m (b - 3))
            else 0) := ⟨_, rfl⟩
  have hcfb : ∀ b, cf b = (row (a0 + a1) m b : ℤ) - (if b = 0 then (2 * x : ℤ) else 0)
      - (if 3 ≤ b then ((row (a0 + a1) m (b - 3) : ℤ) + row kp m (b - 3) - row km m (b - 3))
          else 0) := fun b => by rw [hcf]
  have hRz : (0 : ℤ) < (3 : ℤ) ^ m := by positivity
  have hRm : (R : ℤ) = (3 : ℤ) ^ m := by rw [hR]; push_cast; ring
  have hsmallc : ∀ b, |cf b| < (3 : ℤ) ^ m := by
    intro b
    rw [hcfb b, abs_lt]
    have hA := hArow b
    have hRn : (3 : ℤ) ^ m = 6 * (κ : ℤ) + 3 := by
      rw [← hRm]
      have : R = 6 * κ + 3 := by omega
      rw [this]; push_cast; ring
    have hx4 : 4 * x < R := by omega
    have hxz : 4 * (x : ℤ) < 6 * (κ : ℤ) + 3 := by
      have : ((4 * x : ℕ) : ℤ) < (R : ℤ) := by exact_mod_cast hx4
      push_cast at this
      linarith
    rw [hRn]
    by_cases h0 : b = 0
    · subst h0
      have hA' : ((row (a0 + a1) m 0 : ℕ) : ℤ) ≤ 2 * κ := by exact_mod_cast hA
      rw [if_pos rfl, if_neg (by norm_num)]
      constructor <;> push_cast <;> omega
    · by_cases h3 : 3 ≤ b
      · have hA3 := hArow (b - 3)
        have hp := hprow (b - 3)
        have hmm := hmrow (b - 3)
        rw [if_neg h0, if_pos h3]
        constructor <;> push_cast <;> omega
      · rw [if_neg h0, if_neg h3]
        constructor <;> push_cast <;> omega
  have hsum : ∑ b ∈ range (u + 3), cf b * ((3 : ℤ) ^ m) ^ b = 0 := by
    have hAB3 : a0 + a1 < 3 ^ (m * (u + 3)) :=
      lt_of_lt_of_le hAB (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
    have hA := sum_rows_int hAB3
    have hAu := sum_rows_int hAB
    have hP' := sum_rows_int hkpB
    have hM' := sum_rows_int hkmB
    have hsplit : ∀ b, cf b * ((3 : ℤ) ^ m) ^ b
        = (row (a0 + a1) m b : ℤ) * ((3 : ℤ) ^ m) ^ b
          - (if b = 0 then (2 * x : ℤ) * ((3 : ℤ) ^ m) ^ b else 0)
          - (if 3 ≤ b then (((row (a0 + a1) m (b - 3) : ℤ) + row kp m (b - 3)
              - row km m (b - 3)) * ((3 : ℤ) ^ m) ^ b) else 0) := by
      intro b
      rw [hcfb b]
      split_ifs <;> ring
    simp only [hsplit, Finset.sum_sub_distrib]
    have hI : ∑ b ∈ range (u + 3), (if b = 0 then (2 * x : ℤ) * ((3 : ℤ) ^ m) ^ b else 0)
        = 2 * x := by
      rw [Finset.sum_ite_eq' (range (u + 3)) 0 (fun b => (2 * x : ℤ) * ((3 : ℤ) ^ m) ^ b),
        if_pos (Finset.mem_range.2 (by omega))]
      simp
    have hT : ∑ b ∈ range (u + 3), (if 3 ≤ b then (((row (a0 + a1) m (b - 3) : ℤ)
          + row kp m (b - 3) - row km m (b - 3)) * ((3 : ℤ) ^ m) ^ b) else 0)
        = ((3 : ℤ) ^ m) ^ 3 * (((a0 + a1 : ℕ) : ℤ) + kp - km) := by
      rw [show u + 3 = 3 + u from by ring, Finset.sum_range_add]
      have hlow : ∑ b ∈ range 3, (if 3 ≤ b then (((row (a0 + a1) m (b - 3) : ℤ)
          + row kp m (b - 3) - row km m (b - 3)) * ((3 : ℤ) ^ m) ^ b) else 0) = 0 :=
        Finset.sum_eq_zero fun b hb => by rw [if_neg (by simp at hb; omega)]
      rw [hlow, zero_add, hAu, hP', hM', ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [if_pos (by omega), show 3 + b - 3 = b from by omega, pow_add]
      ring
    rw [hI, hT, ← hA]
    have hz : ((R ^ 3 * (a0 + a1 + kp) + 2 * x : ℕ) : ℤ) = ((a0 + a1 + R ^ 3 * km : ℕ) : ℤ) :=
      congrArg _ htime
    push_cast at hz
    rw [hRm] at hz
    push_cast
    linear_combination (-1 : ℤ) * hz
  have hzero := signed_digits_zero hRz (u + 3) cf hsmallc hsum
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hzero 0 (by omega)
    rw [hcfb 0, if_pos rfl, if_neg (by norm_num)] at h
    have h' : ((row (a0 + a1) m 0 : ℕ) : ℤ) = ((2 * x : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast h'
  · have h := hzero 1 (by omega)
    rw [hcfb 1, if_neg (by norm_num), if_neg (by norm_num)] at h
    have h' : ((row (a0 + a1) m 1 : ℕ) : ℤ) = 0 := by linarith
    exact_mod_cast h'
  · have h := hzero 2 (by omega)
    rw [hcfb 2, if_neg (by norm_num), if_neg (by norm_num)] at h
    have h' : ((row (a0 + a1) m 2 : ℕ) : ℤ) = 0 := by linarith
    exact_mod_cast h'
  · intro b hb3 hbu
    have h := hzero b hbu
    rw [hcfb b, if_neg (by omega), if_pos hb3] at h
    linarith

end History

/-- **The counter history over a compiled deterministic controller.** -/
theorem counter_history100 {P : Controller} {Zon B0 lg : ℕ}
    {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
    {e m u : ℕ}
    (hOk : (P.rom Zon B0).Ok)
    (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
    (hS : Sys100 (P.rom Zon B0) x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k
      o s w τ η ζ γ y)
    (hG : Geometry100 H R q e m u)
    (hGrid : (P.rom Zon B0).Grid P lg)
    (hconv : ∀ ii, ii < P.n → P.f ii = 0 → P.zreq ii = true) :
    ∃ a0 a1 kp km dd, A0 = 2 * a0 ∧ A1 = 2 * a1 ∧ Kp = 2 * kp ∧ Km = 2 * km ∧ D = 2 * dd ∧
      (∀ b, b < u → row kp m b + row km m b = 1) ∧
      (∀ b, row (a0 + a1) m b ≤ (R - 3) / 3 * row dd m b) ∧
      row (a0 + a1) m 0 = 2 * x ∧ row (a0 + a1) m 1 = 0 ∧ row (a0 + a1) m 2 = 0 ∧
      (∀ b, 3 ≤ b → b < u + 3 →
        (row (a0 + a1) m b : ℤ) + row km m (b - 3)
          = row (a0 + a1) m (b - 3) + row kp m (b - 3)) :=
  counter_history_rom100 hOk hP hS hG (P.rom_sidon Zon B0) (P.rom_layout Zon B0)
    (decode_bound100 hOk hP hS hG hGrid hconv)

end Jones1980
