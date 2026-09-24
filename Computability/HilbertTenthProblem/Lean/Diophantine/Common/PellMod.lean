import Diophantine.Common.Pell
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Residues of `ψ_a` modulo `χ_a(n)`, and two auxiliary facts

Mathlib proves, for the first Pell coordinate `χ = xn`, that `χ_i ≡ χ_j (mod χ_n)`
essentially forces `j ≡ ±i (mod 4n)` (`Pell.eq_of_xn_modEq'`).  The
Matijasevič–Robinson Lemma 3.8 of JSWW 1976 uses the analogous statement for the
second coordinate `ψ = yn`, which is proved here:

* `yn_reflect`: `ψ_{n+m} ≡ ψ_{n−m} (mod χ_n)`;
* `xn_dvd_yn_two_mul_add`: `χ_n ∣ ψ_{2n+m} + ψ_m`;
* `yn_modEq_four_mul_add`: `ψ_{4n+m} ≡ ψ_m (mod χ_n)`;
* `eq_zero_of_xn_dvd_yn_add`: for `n ≥ 2` and `i, j ≤ n`, `χ_n ∣ ψ_i + ψ_j` forces `i = j = 0`;
* `yn_modEq_cases`: for `n ≥ 2`, `1 ≤ i ≤ n`, `ψ_j ≡ ψ_i (mod χ_n)` implies `j ≡ ±i (mod 2n)`.

Also: `exists_dvd_yn` (every `m > 0` divides some `ψ_a(t)`, `t ≥ 1`, by pigeonhole),
`IsSquare.of_coprime_mul` (a coprime factor of a square is a square), and
`lt_yn_of_two_le` (`n < ψ_a(n)` for `n ≥ 2`).
-/

namespace Diophantine

open Pell

variable {a : ℕ} (a1 : 1 < a)

/-- `ψ_n < χ_n`. -/
theorem yn_lt_xn (n : ℕ) : yn a1 n < xn a1 n := by
  have h := χ_sq a1 n
  simp only [χ, ψ] at h
  have h4 : 4 ≤ a * a := by nlinarith
  have h3 : 3 ≤ a * a - 1 := by omega
  rw [← Nat.mul_self_lt_mul_self_iff]
  nlinarith [Nat.zero_le (yn a1 n * yn a1 n)]

/-- `χ_{2n} = 2χ_n² − 1` and `ψ_{2n} = 2 χ_n ψ_n`, as integers. -/
theorem xn_two_mul (n : ℕ) : (xn a1 (2 * n) : ℤ) = 2 * (xn a1 n : ℤ) ^ 2 - 1 := by
  have h := xn_add a1 n n
  change xn a1 (n + n) = xn a1 n * xn a1 n + (a * a - 1) * yn a1 n * yn a1 n at h
  have h2 := χ_sq a1 n
  simp only [χ, ψ] at h2
  set D := a * a - 1 with hD
  have h2z : (xn a1 n : ℤ) ^ 2 = (D : ℤ) * (yn a1 n : ℤ) ^ 2 + 1 := by
    have : (xn a1 n * xn a1 n : ℤ) = ((D * yn a1 n * yn a1 n + 1 : ℕ) : ℤ) := by exact_mod_cast h2
    push_cast at this
    linear_combination this
  rw [two_mul, h]
  push_cast
  linear_combination -h2z

theorem yn_two_mul (n : ℕ) : yn a1 (2 * n) = 2 * xn a1 n * yn a1 n := by
  rw [two_mul, yn_add]; ring

/-- Reflection: `ψ_{n+m} = ψ_{n−m} + 2 χ_n ψ_m` for `m ≤ n`. -/
theorem yn_reflect {n m : ℕ} (h : m ≤ n) :
    yn a1 (n + m) = yn a1 (n - m) + 2 * xn a1 n * yn a1 m := by
  have hz := yz_sub a1 h
  simp only [xz, yz] at hz
  have h1 : (yn a1 (n + m) : ℤ) = xn a1 n * yn a1 m + yn a1 n * xn a1 m := by
    rw [yn_add]; push_cast; ring
  have : (yn a1 (n + m) : ℤ) = yn a1 (n - m) + 2 * xn a1 n * yn a1 m := by
    rw [h1, hz]; ring
  exact_mod_cast this

theorem yn_modEq_reflect {n m : ℕ} (h : m ≤ n) :
    yn a1 (n + m) ≡ yn a1 (n - m) [MOD xn a1 n] := by
  rw [yn_reflect a1 h]
  exact (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2
    ⟨2 * yn a1 m, by rw [Nat.add_sub_cancel_left]; ring⟩ |>.symm

/-- `χ_n ∣ ψ_{2n+m} + ψ_m`. -/
theorem xn_dvd_yn_two_mul_add (n m : ℕ) : xn a1 n ∣ yn a1 (2 * n + m) + yn a1 m := by
  have h : (yn a1 (2 * n + m) : ℤ) + yn a1 m
      = xn a1 n * (2 * xn a1 n * yn a1 m + 2 * yn a1 n * xn a1 m) := by
    rw [yn_add, yn_two_mul]
    push_cast
    rw [xn_two_mul]
    ring
  have : (xn a1 n : ℤ) ∣ (yn a1 (2 * n + m) : ℤ) + yn a1 m := ⟨_, h⟩
  exact_mod_cast this

theorem yn_modEq_four_mul_add (n m : ℕ) : yn a1 (4 * n + m) ≡ yn a1 m [MOD xn a1 n] := by
  have h1 := xn_dvd_yn_two_mul_add a1 n (2 * n + m)
  have h2 := xn_dvd_yn_two_mul_add a1 n m
  rw [show 2 * n + (2 * n + m) = 4 * n + m by ring] at h1
  have e1 : yn a1 (4 * n + m) + yn a1 (2 * n + m) ≡ 0 [MOD xn a1 n] :=
    (Nat.modEq_zero_iff_dvd).2 h1
  have e2 : yn a1 m + yn a1 (2 * n + m) ≡ 0 [MOD xn a1 n] := by
    rw [add_comm]; exact (Nat.modEq_zero_iff_dvd).2 h2
  exact Nat.ModEq.add_right_cancel' _ (e1.trans e2.symm)

theorem yn_modEq_four_mul_add' (q n m : ℕ) : yn a1 (4 * n * q + m) ≡ yn a1 m [MOD xn a1 n] := by
  induction q with
  | zero => rw [mul_zero, zero_add]
  | succ q ih =>
    have := yn_modEq_four_mul_add a1 n (4 * n * q + m)
    rw [show 4 * n + (4 * n * q + m) = 4 * n * (q + 1) + m by ring] at this
    exact this.trans ih

/-- Distinct indices `≤ n` give distinct residues of `ψ` modulo `χ_n`. -/
theorem eq_of_yn_modEq_of_le {i j n : ℕ} (hi : i ≤ n) (hj : j ≤ n)
    (h : yn a1 i ≡ yn a1 j [MOD xn a1 n]) : i = j := by
  have hi' : yn a1 i < xn a1 n := lt_of_le_of_lt ((strictMono_y a1).monotone hi) (yn_lt_xn a1 n)
  have hj' : yn a1 j < xn a1 n := lt_of_le_of_lt ((strictMono_y a1).monotone hj) (yn_lt_xn a1 n)
  have := Nat.ModEq.eq_of_lt_of_lt h hi' hj'
  exact (strictMono_y a1).injective this

/-- `2 ψ_{n+1} ≤ χ_{n+1} + ψ_n`, with equality iff `a = 2`. -/
theorem two_yn_succ_le (n : ℕ) : 2 * yn a1 (n + 1) ≤ xn a1 (n + 1) + yn a1 n := by
  have hx := xn_succ a1 n
  change xn a1 (n + 1) = xn a1 n * a + (a * a - 1) * yn a1 n at hx
  have hy := yn_succ a1 n
  have h2 : 2 ≤ a := a1
  have hd : (a * a - 1) + 1 = a * a := Nat.sub_add_cancel (by nlinarith)
  zify [show 1 ≤ a * a by nlinarith] at hx
  zify at hy ⊢
  rw [hx, hy]
  have : (0 : ℤ) ≤ (a : ℤ) - 2 := by
    have : (2 : ℤ) ≤ a := by exact_mod_cast h2
    linarith
  nlinarith [Nat.zero_le (xn a1 n), Nat.zero_le (yn a1 n)]

/-- `ψ_{n+1} + ψ_n < χ_{n+1}`. -/
theorem yn_succ_add_yn_lt (n : ℕ) : yn a1 (n + 1) + yn a1 n < xn a1 (n + 1) := by
  have hx := xn_succ a1 n
  change xn a1 (n + 1) = xn a1 n * a + (a * a - 1) * yn a1 n at hx
  have hy := yn_succ a1 n
  have h2 : 2 ≤ a := a1
  have hxpos : 1 ≤ xn a1 n := x_pos a1 n
  zify [show 1 ≤ a * a by nlinarith] at hx
  zify at hy hxpos ⊢
  rw [hx, hy]
  have : (2 : ℤ) ≤ a := by exact_mod_cast h2
  nlinarith [Nat.zero_le (yn a1 n)]

/-- For `a ≥ 3`, `2 ψ_{n+1} < χ_{n+1}`. -/
theorem two_yn_succ_lt (h3 : 3 ≤ a) (n : ℕ) : 2 * yn a1 (n + 1) < xn a1 (n + 1) := by
  have hx := xn_succ a1 n
  change xn a1 (n + 1) = xn a1 n * a + (a * a - 1) * yn a1 n at hx
  have hy := yn_succ a1 n
  have hxpos : 1 ≤ xn a1 n := x_pos a1 n
  zify [show 1 ≤ a * a by nlinarith] at hx
  zify at hy hxpos ⊢
  rw [hx, hy]
  have : (3 : ℤ) ≤ a := by exact_mod_cast h3
  nlinarith [Nat.zero_le (yn a1 n)]

/-- For `a = 2`, `2 ψ_{n+1} = χ_{n+1} + ψ_n`. -/
theorem two_yn_succ_eq (h2 : a = 2) (n : ℕ) : 2 * yn a1 (n + 1) = xn a1 (n + 1) + yn a1 n := by
  have hx := xn_succ a1 n
  change xn a1 (n + 1) = xn a1 n * a + (a * a - 1) * yn a1 n at hx
  have hy := yn_succ a1 n
  subst h2
  rw [hx, hy]
  norm_num
  ring

/-- For `n ≥ 2` and `i, j ≤ n`, `χ_n ∣ ψ_i + ψ_j` only when `i = j = 0`. -/
theorem eq_zero_of_xn_dvd_yn_add {i j n : ℕ} (hn : 2 ≤ n) (hi : i ≤ n) (hj : j ≤ n)
    (h : xn a1 n ∣ yn a1 i + yn a1 j) : i = 0 ∧ j = 0 := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  by_contra hne
  have hpos : 0 < yn a1 i + yn a1 j := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have : j ≠ 0 := fun hj0 => hne ⟨rfl, hj0⟩
      have := strictMono_y a1 (Nat.pos_of_ne_zero this)
      simp [yn_zero] at this ⊢; omega
    · have := strictMono_y a1 hi0
      simp [yn_zero] at this; omega
  have hle : xn a1 (n' + 1) ≤ yn a1 i + yn a1 j := Nat.le_of_dvd hpos h
  -- either both indices are n, or the sum is at most ψ_n + ψ_{n-1} < χ_n
  by_cases hij : i = n' + 1 ∧ j = n' + 1
  · obtain ⟨rfl, rfl⟩ := hij
    have h1 := two_yn_succ_le a1 n'
    have h2 : yn a1 n' < xn a1 (n' + 1) :=
      lt_of_lt_of_le (strictMono_y a1 (Nat.lt_succ_self n')) (yn_lt_xn a1 _).le
    -- the sum 2ψ_n is a multiple of χ_n, so equals χ_n (as it is < 2χ_n), then compare
    obtain ⟨q, hq⟩ := h
    have hq1 : q = 1 := by
      have : 2 * yn a1 (n' + 1) < 2 * xn a1 (n' + 1) := by
        have := yn_lt_xn a1 (n' + 1); omega
      rcases Nat.lt_or_ge q 2 with hq2 | hq2
      · interval_cases q <;> omega
      · exfalso; nlinarith
    subst hq1
    rw [mul_one] at hq
    rcases Nat.lt_or_ge a 3 with ha | ha
    · have ha2 : a = 2 := by omega
      have := two_yn_succ_eq a1 ha2 n'
      have : yn a1 n' = 0 := by omega
      have := (strictMono_y a1).injective (this.trans (yn_zero a1).symm)
      omega
    · have := two_yn_succ_lt a1 ha n'
      omega
  · have hsum : yn a1 i + yn a1 j ≤ yn a1 (n' + 1) + yn a1 n' := by
      have mono := (strictMono_y a1).monotone
      rcases Nat.lt_or_ge i (n' + 1) with hi' | hi'
      · have := mono (Nat.le_of_lt_succ hi'); have := mono hj; omega
      · have hi'' : i = n' + 1 := by omega
        have hj' : j < n' + 1 := by
          by_contra hc; push_neg at hc; exact hij ⟨hi'', by omega⟩
        have := mono (Nat.le_of_lt_succ hj'); have := mono hi; omega
    have := yn_succ_add_yn_lt a1 n'
    omega

/-- The residue classes of `ψ` modulo `χ_n`: for `n ≥ 2` and `1 ≤ i ≤ n`,
`ψ_j ≡ ψ_i (mod χ_n)` forces `j ≡ i` or `j ≡ −i (mod 2n)`. -/
theorem yn_modEq_cases {i j n : ℕ} (hn : 2 ≤ n) (hi1 : 1 ≤ i) (hin : i ≤ n)
    (h : yn a1 j ≡ yn a1 i [MOD xn a1 n]) :
    ∃ q, j = i + 2 * n * q ∨ j + i = 2 * n * q := by
  have h4n : 0 < 4 * n := by omega
  set ρ := j % (4 * n) with hρ
  set q4 := j / (4 * n) with hq4
  have hj : j = 4 * n * q4 + ρ := by rw [hρ, hq4]; exact (Nat.div_add_mod j (4 * n)).symm
  have hρlt : ρ < 4 * n := Nat.mod_lt _ h4n
  have hρ_mod : yn a1 ρ ≡ yn a1 i [MOD xn a1 n] :=
    (yn_modEq_four_mul_add' a1 q4 n ρ).symm.trans (hj ▸ h)
  rcases Nat.lt_or_ge n ρ with hρn | hρn
  · rcases Nat.lt_or_ge (2 * n) ρ with hρ2n | hρ2n
    · -- 2n < ρ < 4n: ψ_ρ ≡ −ψ_{ρ−2n}, contradiction with the sum lemma
      exfalso
      set m := ρ - 2 * n with hm
      have hρm : ρ = 2 * n + m := by omega
      have hdvd := xn_dvd_yn_two_mul_add a1 n m
      rw [← hρm] at hdvd
      have hsum : xn a1 n ∣ yn a1 i + yn a1 m := by
        have e1 : yn a1 ρ + yn a1 m ≡ 0 [MOD xn a1 n] := (Nat.modEq_zero_iff_dvd).2 hdvd
        have e2 : yn a1 i + yn a1 m ≡ yn a1 ρ + yn a1 m [MOD xn a1 n] :=
          Nat.ModEq.add_right _ hρ_mod.symm
        exact (Nat.modEq_zero_iff_dvd).1 (e2.trans e1)
      rcases Nat.lt_or_ge n m with hmn | hmn
      · -- reflect m to 2n − m
        have hm2 : m - n ≤ n := by omega
        have hr := yn_modEq_reflect a1 hm2
        rw [show n + (m - n) = m by omega, show n - (m - n) = 2 * n - m by omega] at hr
        have hsum' : xn a1 n ∣ yn a1 i + yn a1 (2 * n - m) := by
          have e1 : yn a1 i + yn a1 m ≡ 0 [MOD xn a1 n] := (Nat.modEq_zero_iff_dvd).2 hsum
          have e2 : yn a1 i + yn a1 (2 * n - m) ≡ yn a1 i + yn a1 m [MOD xn a1 n] :=
            Nat.ModEq.add_left _ hr.symm
          exact (Nat.modEq_zero_iff_dvd).1 (e2.trans e1)
        have := eq_zero_of_xn_dvd_yn_add a1 hn hin (by omega) hsum'
        omega
      · have := eq_zero_of_xn_dvd_yn_add a1 hn hin hmn hsum
        omega
    · -- n < ρ ≤ 2n: reflect
      have hm : ρ - n ≤ n := by omega
      have hr := yn_modEq_reflect a1 hm
      rw [show n + (ρ - n) = ρ by omega] at hr
      have := eq_of_yn_modEq_of_le a1 (by omega) hin (hr.symm.trans hρ_mod)
      refine ⟨2 * q4 + 1, Or.inr ?_⟩
      have e : 2 * n * (2 * q4 + 1) = 4 * n * q4 + 2 * n := by ring
      omega
  · -- ρ ≤ n
    have := eq_of_yn_modEq_of_le a1 hρn hin hρ_mod
    have e : 2 * n * (2 * q4) = 4 * n * q4 := by ring
    exact ⟨2 * q4, Or.inl (by omega)⟩

/-! ### Auxiliary facts -/

/-- Every `m > 0` divides some `ψ_a(t)` with `t ≥ 1` (pigeonhole on the pairs `(χ_t, ψ_t)` mod `m`). -/
theorem exists_dvd_yn {m : ℕ} (hm : 0 < m) : ∃ t, 0 < t ∧ m ∣ yn a1 t := by
  haveI : NeZero m := ⟨hm.ne'⟩
  let f : ℕ → ZMod m × ZMod m := fun t => ((xn a1 t : ZMod m), (yn a1 t : ZMod m))
  obtain ⟨s, t, hst, hf⟩ := Finite.exists_ne_map_eq_of_infinite f
  -- WLOG s < t
  wlog hlt : s < t generalizing s t
  · exact this t s hst.symm hf.symm (lt_of_le_of_ne (not_lt.1 hlt) hst.symm)
  refine ⟨t - s, by omega, ?_⟩
  simp only [f, Prod.mk.injEq] at hf
  obtain ⟨hx, hy⟩ := hf
  have hz := yz_sub a1 hlt.le
  simp only [xz, yz] at hz
  have : ((yn a1 (t - s) : ℤ) : ZMod m) = 0 := by
    rw [hz]
    push_cast
    rw [hx, hy]
    ring
  rw [Int.cast_natCast] at this
  exact (ZMod.natCast_eq_zero_iff _ _).1 this

/-- A coprime factor of a square is a square. -/
theorem IsSquare.of_coprime_mul {a b : ℕ} (h : Nat.Coprime a b) (hs : IsSquare (a * b)) :
    IsSquare a := by
  obtain ⟨c, hc⟩ := hs
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨0, rfl⟩
  -- g = gcd a c; a = a' g, c = c' g with a' ⊥ c'
  obtain ⟨g, a', c', hg, hcop, rfl, rfl⟩ := Nat.exists_coprime' (show 0 < Nat.gcd a c from
    Nat.gcd_pos_of_pos_left _ ha)
  -- (a' g) b = (c' g)²  ⇒  a' b = g c'²
  have key : a' * b = g * (c' * c') := by
    have : g * (a' * b) = g * (g * (c' * c')) := by
      calc g * (a' * b) = a' * g * b := by ring
        _ = c' * g * (c' * g) := hc
        _ = g * (g * (c' * c')) := by ring
    exact Nat.eq_of_mul_eq_mul_left hg this
  -- a' ∣ g (since a' ⊥ c'²) and g ∣ a' (since g ⊥ b)
  have h1 : a' ∣ g := by
    have : a' ∣ g * (c' * c') := Dvd.intro b key
    exact (hcop.mul_right hcop).dvd_of_dvd_mul_right this
  have h2 : g ∣ a' := by
    have hgb : Nat.Coprime g b := Nat.Coprime.coprime_mul_left h
    have : g ∣ a' * b := Dvd.intro _ key.symm
    exact hgb.dvd_of_dvd_mul_right this
  have : a' = g := Nat.dvd_antisymm h1 h2
  exact ⟨g, by rw [this]⟩

/-- `n < ψ_a(n)` for `n ≥ 2`. -/
theorem lt_yn_of_two_le {n : ℕ} (hn : 2 ≤ n) : n < yn a1 n := by
  have h := pow_le_ψ_succ a1 (n - 1)
  rw [Nat.sub_add_cancel (by omega)] at h
  have h3 : 3 ^ (n - 1) ≤ (2 * a - 1) ^ (n - 1) := Nat.pow_le_pow_left (by omega) _
  have h4 : n + 1 ≤ 3 ^ (n - 1) := by
    clear h h3
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [show n + 1 - 1 = n - 1 + 1 by omega, pow_succ]
      omega
  simp only [ψ] at h
  omega

end Diophantine
