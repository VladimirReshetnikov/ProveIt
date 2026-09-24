import Diophantine.Paper1980.Bootstrap100
import Diophantine.Paper1980.TagRows

/-!
# Radix geometry of the 100-operation counter system

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §2 (end).  After the kernel (`q = 3^e`):
`W = R³` and `q = W v` make `R` a power of three, `R = 3^m`; the head equation
`H(R − 1) = 2J = 2(q − 1)` then forces `m ∣ e` — a nonzero remainder `s < m` would need
`3^m − 1 ∣ 2(3^s − 1)` with `0 < 2(3^s − 1) < 3^m − 1` — so `q = R^u` and `H` is twice the
row-head word `heads m u`, with `u ≥ 3` because `R³ ∣ q`.
-/

namespace Jones1980

open Ternary

/-- If `3^m − 1 ∣ 2(3^e − 1)` with `m ≥ 1`, then `m ∣ e`. -/
theorem dvd_of_two_mul_pow_sub_one_dvd {m e : ℕ} (hm : 1 ≤ m)
    (h : 3 ^ m - 1 ∣ 2 * (3 ^ e - 1)) : m ∣ e := by
  obtain ⟨t, s, hs, rfl⟩ : ∃ t s, s < m ∧ e = m * t + s :=
    ⟨e / m, e % m, Nat.mod_lt _ (by omega), (Nat.div_add_mod e m).symm⟩
  have h1 : 3 ^ m - 1 ∣ (3 ^ m) ^ t - 1 := Nat.sub_one_dvd_pow_sub_one (3 ^ m) t
  have ha : 1 ≤ (3 ^ m) ^ t := Nat.one_le_pow _ _ (by positivity)
  have hb : 1 ≤ 3 ^ s := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 2 * (3 ^ (m * t + s) - 1)
      = (2 * 3 ^ s) * ((3 ^ m) ^ t - 1) + 2 * (3 ^ s - 1) := by
    have hx : (2 * 3 ^ s) * ((3 ^ m) ^ t - 1) = 2 * 3 ^ s * (3 ^ m) ^ t - 2 * 3 ^ s := by
      rw [Nat.mul_sub, mul_one]
    have hy : (3 : ℕ) ^ (m * t + s) = (3 ^ m) ^ t * 3 ^ s := by rw [pow_add, pow_mul]
    have hz : 2 * 3 ^ s * (3 ^ m) ^ t = 2 * ((3 ^ m) ^ t * 3 ^ s) := by ring
    have hc : 3 ^ s ≤ (3 ^ m) ^ t * 3 ^ s := Nat.le_mul_of_pos_left _ (by positivity)
    rw [hx, hy, hz]
    omega
  have h4 : 3 ^ m - 1 ∣ (2 * 3 ^ s) * ((3 ^ m) ^ t - 1) := Dvd.dvd.mul_left h1 _
  have h3 : 3 ^ m - 1 ∣ 2 * (3 ^ s - 1) := by
    rw [h2] at h
    exact (Nat.dvd_add_right h4).1 h
  have h5 : 2 * (3 ^ s - 1) < 3 ^ m - 1 := by
    have h6 : 3 ^ s ≤ 3 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h7 : (3 : ℕ) ^ m = 3 * 3 ^ (m - 1) := by rw [← pow_succ', Nat.sub_add_cancel hm]
    have h8 : 1 ≤ 3 ^ (m - 1) := Nat.one_le_pow _ _ (by norm_num)
    omega
  have h9 : 2 * (3 ^ s - 1) = 0 := Nat.eq_zero_of_dvd_of_lt h3 h5
  have h10 : s = 0 := by
    by_contra hne
    have : (3 : ℕ) ^ 1 ≤ 3 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst h10
  exact ⟨t, by omega⟩

/-- The doubled head equation `H(R − 1) = 2(q − 1)` with `q = 3^e`, `R = 3^m`, `m ≥ 1`:
then `e = m u` and `H = 2 · heads m u`. -/
theorem heads_of_doubled_head_eq {H m e : ℕ} (hm : 1 ≤ m)
    (hH : H * (3 ^ m - 1) = 2 * (3 ^ e - 1)) : ∃ u, e = m * u ∧ H = 2 * heads m u := by
  obtain ⟨u, hu⟩ : m ∣ e := dvd_of_two_mul_pow_sub_one_dvd hm ⟨H, by rw [← hH]; ring⟩
  refine ⟨u, hu, ?_⟩
  have h1 := heads_mul_sub_one m u
  rw [← hu] at h1
  have h2 : 1 ≤ 3 ^ e := Nat.one_le_pow _ _ (by norm_num)
  have h3 : H * (3 ^ m - 1) = (2 * heads m u) * (3 ^ m - 1) := by
    rw [hH]
    have : (2 * heads m u) * (3 ^ m - 1) = 2 * (heads m u * (3 ^ m - 1)) := by ring
    omega
  have h4 : 0 < 3 ^ m - 1 := by
    have : (3 : ℕ) ^ 1 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  exact Nat.eq_of_mul_eq_mul_right h4 h3

/-- The recovered geometry of a solution of the 100-operation system. -/
structure Geometry100 (H R q : ℕ) (e m u : ℕ) : Prop where
  hq : q = 3 ^ e
  hR : R = 3 ^ m
  he : e = m * u
  hm : 1 ≤ m
  hu : 3 ≤ u
  hH : H = 2 * heads m u

section Geometry

variable {C : ROM100}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)

include hP hS

theorem geometry100 (hZ : 81 ≤ C.Zon) (hB : 9 ≤ C.B0) :
    ∃ e m u, Geometry100 H R q e m u := by
  obtain ⟨⟨e, he1, hqe⟩, -, -⟩ := kernel_out100 hP hS hZ hB
  -- `R` is a power of three
  have hR3q : R ^ 3 ∣ q := by rw [hS.E1, ← hS.E19]; exact Dvd.intro v rfl
  have hRq : R ∣ q := dvd_trans (dvd_pow_self R (by norm_num)) hR3q
  rw [hqe] at hRq hR3q
  obtain ⟨m, hme, hRm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hRq
  have hR9 : 9 ≤ R := by
    have := R_ge100 hP hS hB
    omega
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hRm; omega
    · exact h0
  -- the head equation
  have hhead : H * (3 ^ m - 1) = 2 * (3 ^ e - 1) := by
    have h2 := hS.E2
    have h0 := hS.E0
    have hq1 : 1 ≤ q := hP.q
    rw [← hRm, ← hqe]
    have hcomm : R * H = H * R := mul_comm _ _
    have hsub : H * (R - 1) = R * H - H := by rw [Nat.mul_sub, mul_one, mul_comm]
    rw [hsub]
    omega
  obtain ⟨u, heu, hHu⟩ := heads_of_doubled_head_eq hm1 hhead
  -- `u ≥ 3`
  have hu3 : 3 ≤ u := by
    have h1 : (3 : ℕ) ^ (m * 3) ≤ 3 ^ e := by
      rw [pow_mul]
      have h : R ^ 3 ≤ 3 ^ e := Nat.le_of_dvd (by positivity) hR3q
      rw [hRm] at h
      exact h
    have h2 : m * 3 ≤ e := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    rw [heu] at h2
    nlinarith
  exact ⟨e, m, u, hqe, hRm, heu, hm1, hu3, hHu⟩

end Geometry

end Jones1980
