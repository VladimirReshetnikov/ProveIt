import DiophantineConsistency.Compact44.P72Early
import Mathlib.Tactic.IntervalCases

/-! # Package 62: the early index congruence for the modulus `U = 4q⁴`

As in `P72Early`: the first norm gives `k = 2n + 4XY²·s`, and `U ∣ 4XY²`
because `X = wq` and `Y = sq³`. So the main carrier modulo `U` gives
`(H·2n) % U = (H(R+1)) % U`. The gcd cancellation leaves `μ = U/g0` with
`g0 = gcd(U, H)`, and `g0 ∣ 3` (`gcd_dvd_three`):

* `H = 3 + q³m` gives `36 + 4H·q³m = 12H + 4q⁴·q²m²`, so `g0 ∣ 36`. `H` is
  odd, so `g0` is odd and `g0 ∣ 9`;
* `g0 = 9` is impossible. If `3 ∤ q` then `4q⁴ ≡ 1 (mod 3)`. If `q = 3t`, then
  `H = 3 + 9·3t³m ≡ 3 (mod 9)`.

Hence `U ≤ 3μ`, and `3(R+1) < 3q⁴ < U ≤ 3μ` gives `(2n) % μ = R + 1`. Unlike
P13, `q` may be divisible by `3` here, since `J` is free. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace P62Early
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ArithmeticGcdNormalization ArithmeticPellRecurrence
open ArithmeticPellCongruences P72Mu
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem mod_one_add_mul (b K : V) (hb : 1 < b) : (1 + b * K) % b = 1 := by
  rw [mod_add_mul' _ _ (lt_trans (by simp) hb)]; exact mod_eq_self_of_lt hb

/-- A common divisor of `4q⁴` and `H = 3 + q³m`, with `H` odd, divides `3`. -/
theorem gcd_dvd_three (q m g0 : V) (hgU : g0 ∣ 4 * ((q * q) * (q * q)))
    (hgH : g0 ∣ 3 + q * q * q * m) (hodd : (3 + q * q * q * m) % 2 = 1) : g0 ∣ 3 := by
  set H : V := 3 + q * q * q * m with hHdef
  obtain ⟨h', hh'⟩ := hgH
  obtain ⟨u', hu'⟩ := hgU
  have hH0 : 0 < H := add_pos_of_pos_of_nonneg (by norm_num) (Arithmetic.zero_le _)
  have hg0 : 0 < g0 := by
    rcases (Arithmetic.zero_le g0).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, zero_mul] at hh'; exact (ne_of_gt hH0) hh'
  -- g0 ∣ 36
  have e : 36 + g0 * (4 * h' * (q * q * q * m)) = g0 * (12 * h' + u' * (q * q * m * m)) := by
    have e0 : 36 + 4 * H * (q * q * q * m) = 12 * H + 4 * ((q * q) * (q * q)) * (q * q * m * m) := by
      rw [hHdef]; ring
    calc 36 + g0 * (4 * h' * (q * q * q * m)) = 36 + 4 * H * (q * q * q * m) := by rw [hh']; ring
      _ = 12 * H + 4 * ((q * q) * (q * q)) * (q * q * m * m) := e0
      _ = g0 * (12 * h' + u' * (q * q * m * m)) := by rw [hh', hu']; ring
  have h36 : g0 ∣ 36 := by
    apply mod_eq_zero_iff_dvd.mp
    have h1 := congrArg (fun x : V => x % g0) e
    rw [mod_add_mul' _ _ hg0] at h1
    rw [h1]; exact mod_eq_zero_iff_dvd.mpr ⟨_, rfl⟩
  -- g0 is odd
  have hr2 : g0 % 2 < 2 := mod_lt _ (by norm_num)
  obtain ⟨r, hr⟩ := eq_nat_of_lt_nat (n := 2) hr2
  have hr1 : r < 2 := by exact_mod_cast (hr ▸ hr2 : ((r : ℕ) : V) < 2)
  have hodd0 : g0 % 2 = 1 := by
    interval_cases r
    · exfalso
      have h2 : 2 ∣ g0 := mod_eq_zero_iff_dvd.mp (by simpa using hr)
      have h2H : 2 ∣ H := dvd_trans h2 ⟨h', hh'⟩
      have := mod_eq_zero_iff_dvd.mpr h2H
      rw [hodd] at this; exact _root_.one_ne_zero this
    · simpa using hr
  have hu := div_add_mod g0 2
  rw [hodd0] at hu
  set u := g0 / 2
  have hbez : Bez 4 g0 1 := ⟨u * u + u, 0, 0, g0, by rw [← hu]; ring⟩
  have h9 : g0 ∣ 9 := unit_certificate_cancel hbez (by
    have : (36 : V) = 4 * 9 := by norm_num
    rwa [this] at h36)
  -- g0 is a small numeral
  obtain ⟨ee, hee⟩ := h9
  have hg9 : g0 < 10 := lt_of_le_of_lt (Arithmetic.le_of_dvd (by norm_num) ⟨ee, hee⟩) (by norm_num)
  have he0 : 0 < ee := by
    rcases (Arithmetic.zero_le ee).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hee; exact absurd hee (by norm_num)
  have he9 : ee < 10 := lt_of_le_of_lt (Arithmetic.le_of_dvd (show (0 : V) < 9 by norm_num)
    (show ee ∣ (9 : V) from ⟨g0, by rw [hee]; ring⟩)) (show (9 : V) < 10 by norm_num)
  obtain ⟨n, rfl⟩ := eq_nat_of_lt_nat (n := 10) hg9
  obtain ⟨n', rfl⟩ := eq_nat_of_lt_nat (n := 10) he9
  have hnn : n * n' = 9 := by
    have : ((n * n' : ℕ) : V) = ((9 : ℕ) : V) := by push_cast; exact hee.symm
    exact_mod_cast this
  have hn10 : n < 10 := by exact_mod_cast hg9
  interval_cases n
  all_goals (try (exfalso; omega))
  · exact ⟨3, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  -- n = 9
  exfalso
  have h9U : (9 : V) ∣ 4 * ((q * q) * (q * q)) := ⟨u', by simpa using hu'⟩
  have h9H : (9 : V) ∣ H := ⟨h', by simpa using hh'⟩
  have hr3 : q % 3 < 3 := mod_lt _ (by norm_num)
  obtain ⟨r3, hr3'⟩ := eq_nat_of_lt_nat (n := 3) hr3
  have hr3n : r3 < 3 := by exact_mod_cast (hr3' ▸ hr3 : ((r3 : ℕ) : V) < 3)
  have hq := div_add_mod q 3
  rw [hr3'] at hq
  set t := q / 3
  have h3U : (3 : V) ∣ 4 * ((q * q) * (q * q)) := dvd_trans ⟨3, by norm_num⟩ h9U
  have h3U0 := mod_eq_zero_iff_dvd.mpr h3U
  interval_cases r3
  · -- q = 3t: H ≡ 3 (mod 9)
    have hq' : q = 3 * t := by simpa using hq.symm
    have e9 : H = 3 + 9 * (3 * t * t * t * m) := by rw [hHdef, hq']; ring
    have h0 := mod_eq_zero_iff_dvd.mpr h9H
    rw [e9, mod_add_mul' _ _ (by norm_num), mod_eq_self_of_lt (by norm_num)] at h0
    exact absurd h0 (by norm_num)
  · -- q = 3t + 1
    have hq' : q = 3 * t + 1 := by simpa using hq.symm
    have e3 : 4 * ((q * q) * (q * q)) =
        1 + 3 * (108 * t * t * t * t + 144 * t * t * t + 72 * t * t + 16 * t + 1) := by
      rw [hq']; ring
    rw [e3, mod_one_add_mul _ _ (by norm_num)] at h3U0
    exact _root_.one_ne_zero h3U0
  · -- q = 3t + 2
    have hq' : q = 3 * t + 2 := by simpa using hq.symm
    have e3 : 4 * ((q * q) * (q * q)) =
        1 + 3 * (108 * t * t * t * t + 288 * t * t * t + 288 * t * t + 128 * t + 21) := by
      rw [hq']; ring
    rw [e3, mod_one_add_mul _ _ (by norm_num)] at h3U0
    exact _root_.one_ne_zero h3U0

theorem early (q X Y k R H U g c a γ w s τ : V)
    (hq3 : 3 ≤ q) (hw : 0 < w) (hs : 0 < s) (hX : X = w * q) (hYq : Y = s * (q * q * q))
    (hH : H = 4 * a + 3) (ha : a = X * Y + Y) (hU : U = 4 * ((q * q) * (q * q)))
    (hτ : τ * τ = 1 + ((X * Y) * Y) * (((X * Y) * Y) + 1) * k * k)
    (hcar : U * g + H * k = U * (X + a * c) + H * (U * γ + R + 1))
    (hwin : R + 1 < q * (q * (q * q))) :
    ∃ n s' μ : V, 2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k ∧
      xcoord n (2 * ((X * Y) * Y - 1) + 1) = τ ∧ n ≤ k ∧
      k = 2 * n + 4 * ((X * Y) * Y) * s' ∧ 0 < μ ∧ R + 1 < μ ∧
      (2 * n) % μ = R + 1 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq3
  have hX0 : 0 < X := by rw [hX]; exact mul_pos hw hq0
  have hY0 : 0 < Y := by rw [hYq]; exact mul_pos hs (mul_pos (mul_pos hq0 hq0) hq0)
  have hQ : 0 < (X * Y) * Y := mul_pos (mul_pos hX0 hY0) hY0
  obtain ⟨n, hnk, hnx, hny⟩ :=
    ArithmeticPellFirstNorm.positive_parameter_solution ((X * Y) * Y) τ k hQ hτ
  have hQ1 : (X * Y) * Y - 1 + 1 = (X * Y) * Y := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hB : 2 * ((X * Y) * Y) ∣ 2 * ((X * Y) * Y - 1) + 1 + 1 :=
    ⟨1, by calc 2 * ((X * Y) * Y - 1) + 1 + 1 = 2 * ((X * Y) * Y - 1 + 1) := by ring
      _ = 2 * ((X * Y) * Y) * 1 := by rw [hQ1]; ring⟩
  obtain ⟨_, s', _, hys⟩ := residue_quotients n (2 * ((X * Y) * Y - 1) + 1) (2 * ((X * Y) * Y)) hB
  have hks : k = 2 * n + 4 * ((X * Y) * Y) * s' := by rw [← hny, hys]; ring
  -- the carrier modulo U
  have hU0 : 0 < U := by rw [hU]; exact mul_pos (by norm_num) (mul_pos (mul_pos hq0 hq0) (mul_pos hq0 hq0))
  have e1 : U * g + H * k = H * (2 * n) + U * (g + H * (w * s * s * q * q * q * s')) := by
    rw [hks, hU, hX, hYq]; ring
  have e2 : U * (X + a * c) + H * (U * γ + R + 1) = H * (R + 1) + U * ((X + a * c) + H * γ) := by
    ring
  have hmodU : (H * (2 * n)) % U = (H * (R + 1)) % U := by
    have h : (U * g + H * k) % U = (U * (X + a * c) + H * (U * γ + R + 1)) % U :=
      congrArg (fun z : V => z % U) hcar
    rwa [e1, e2, mod_add_mul' _ _ hU0, mod_add_mul' _ _ hU0] at h
  obtain ⟨g0, μ, hg0, hUμ, hg0H, hμ0, hmod⟩ := gcd_cancel U H (2 * n) (R + 1) hU0 hmodU
  -- g0 divides 3
  have eH : H = 3 + q * q * q * (4 * s * (w * q + 1)) := by rw [hH, ha, hX, hYq]; ring
  have hodd : (3 + q * q * q * (4 * s * (w * q + 1))) % 2 = 1 := by
    have : 3 + q * q * q * (4 * s * (w * q + 1)) = 1 + 2 * (1 + 2 * (q * q * q * s * (w * q + 1))) := by ring
    rw [this]; exact mod_one_add_mul _ _ (by norm_num)
  have hgU : g0 ∣ 4 * ((q * q) * (q * q)) := ⟨μ, by rw [← hU, hUμ]⟩
  have hgH : g0 ∣ 3 + q * q * q * (4 * s * (w * q + 1)) := by rw [← eH]; exact hg0H
  have hg3 : g0 ∣ 3 := gcd_dvd_three q (4 * s * (w * q + 1)) g0 hgU hgH hodd
  have hg0le : g0 ≤ 3 := Arithmetic.le_of_dvd (by norm_num) hg3
  have hU3 : U ≤ 3 * μ := by rw [hUμ]; exact mul_le_mul_of_nonneg_right hg0le (Arithmetic.zero_le _)
  have hRμ : R + 1 < μ := by
    have h1 : 3 * (R + 1) < 3 * (q * (q * (q * q))) := mul_lt_mul_of_pos_left hwin (by norm_num)
    have h2 : 3 * (q * (q * (q * q))) ≤ U := by
      rw [hU]
      calc 3 * (q * (q * (q * q))) ≤ 4 * (q * (q * (q * q))) :=
            mul_le_mul_of_nonneg_right (by norm_num) (Arithmetic.zero_le _)
        _ = 4 * ((q * q) * (q * q)) := by ring
    have h3 : 3 * (R + 1) < 3 * μ := lt_of_lt_of_le h1 (le_trans h2 hU3)
    exact lt_of_mul_lt_mul_left h3 (Arithmetic.zero_le _)
  refine ⟨n, s', μ, hny, hnx, hnk, hks, hμ0, hRμ, ?_⟩
  rw [hmod]
  exact mod_eq_self_of_lt hRμ

end P62Early

#print axioms P62Early.gcd_dvd_three
#print axioms P62Early.early
