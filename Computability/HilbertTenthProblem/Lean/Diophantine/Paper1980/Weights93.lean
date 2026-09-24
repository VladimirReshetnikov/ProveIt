import Mathlib.Tactic

/-!
# Uniqueness of monomial weights `3ⁱ + 3ᵏ`

The physical coordinate `i` has weight `vᵢ = 6·3ⁱ`; the quadratic monomials of
a row have weights `0` (`x²`), `vᵢ` (`x zᵢ`), `2vᵢ` (`zᵢ²`) and `vᵢ + v_k`
(`zᵢ z_k`, `i ≠ k`).  These weights determine the monomial: this file proves
the underlying facts about powers of three.
-/

namespace Jones1980

namespace Weights

/-- `3ⁱ ≠ 2·3ᵃ`. -/
theorem pow_ne_two_mul : ∀ i a : ℕ, 3 ^ i ≠ 2 * 3 ^ a
  | 0, a => by
    intro h
    have : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by norm_num)
    omega
  | i + 1, 0 => by
    intro h
    have : 3 ∣ 3 ^ (i + 1) := dvd_pow_self 3 (by omega)
    rw [h] at this
    omega
  | i + 1, a + 1 => by
    intro h
    rw [pow_succ, pow_succ] at h
    have := pow_ne_two_mul i a
    omega

/-- `3ⁱ ≠ 3ᵃ + 3ᵇ`. -/
theorem pow_ne_add : ∀ i a b : ℕ, 3 ^ i ≠ 3 ^ a + 3 ^ b
  | 0, a, b => by
    intro h
    have : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by norm_num)
    have : 1 ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
    omega
  | i + 1, 0, b => by
    intro h
    have h3 : 3 ∣ 3 ^ (i + 1) := dvd_pow_self 3 (by omega)
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; rw [h] at h3; omega
    · have : 3 ∣ 3 ^ b := dvd_pow_self 3 hb.ne'
      rw [h] at h3
      have := (Nat.dvd_add_right this).1 (by rwa [add_comm] at h3)
      omega
  | i + 1, a + 1, 0 => by
    intro h
    have h3 : 3 ∣ 3 ^ (i + 1) := dvd_pow_self 3 (by omega)
    have : 3 ∣ 3 ^ (a + 1) := dvd_pow_self 3 (by omega)
    rw [h] at h3
    have := (Nat.dvd_add_right this).1 h3
    omega
  | i + 1, a + 1, b + 1 => by
    intro h
    rw [pow_succ, pow_succ, pow_succ] at h
    have := pow_ne_add i a b
    omega

/-- `2·3ⁱ = 3ᵃ + 3ᵇ` forces `a = b = i`. -/
theorem two_mul_pow_eq_add : ∀ i a b : ℕ, 2 * 3 ^ i = 3 ^ a + 3 ^ b → a = i ∧ b = i
  | 0, a, b => by
    intro h
    have ha : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by norm_num)
    have hb : 1 ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
    have ha' : 3 ^ a = 1 := by omega
    have hb' : 3 ^ b = 1 := by omega
    exact ⟨Nat.pow_eq_one.1 ha' |>.resolve_left (by norm_num),
      Nat.pow_eq_one.1 hb' |>.resolve_left (by norm_num)⟩
  | i + 1, a, b => by
    intro h
    have h3 : 3 ∣ 2 * 3 ^ (i + 1) := Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) 2
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb; simp only [pow_zero] at h; omega
      · have : 3 ∣ 3 ^ b := dvd_pow_self 3 hb.ne'
        rw [h] at h3
        have := (Nat.dvd_add_left this).1 h3
        omega
    · rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb
        have : 3 ∣ 3 ^ a := dvd_pow_self 3 ha.ne'
        rw [h] at h3
        have := (Nat.dvd_add_right this).1 h3
        omega
      · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        rw [pow_succ, pow_succ, pow_succ] at h
        have := two_mul_pow_eq_add i a' b' (by omega)
        omega

/-- `3ⁱ + 3ᵏ = 3ᵃ + 3ᵇ` forces `{i, k} = {a, b}`. -/
theorem add_pow_eq_add : ∀ i k a b : ℕ, 3 ^ i + 3 ^ k = 3 ^ a + 3 ^ b →
    (i = a ∧ k = b) ∨ (i = b ∧ k = a)
  | 0, 0, a, b => by
    intro h
    have := two_mul_pow_eq_add 0 a b (by simpa using h)
    omega
  | 0, k + 1, a, b => by
    intro h
    have hk : 3 ∣ 3 ^ (k + 1) := dvd_pow_self 3 (by omega)
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      have : 3 ^ (k + 1) = 3 ^ b := by simp only [pow_zero] at h; omega
      left; exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3) this⟩
    · rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb
        have : 3 ^ (k + 1) = 3 ^ a := by simp only [pow_zero] at h; omega
        right; exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3) this⟩
      · exfalso
        have ha3 : 3 ∣ 3 ^ a := dvd_pow_self 3 ha.ne'
        have hb3 : 3 ∣ 3 ^ b := dvd_pow_self 3 hb.ne'
        have : 3 ∣ 3 ^ 0 + 3 ^ (k + 1) := by rw [h]; exact dvd_add ha3 hb3
        have := (Nat.dvd_add_left hk).1 this
        norm_num at this
  | i + 1, 0, a, b => by
    intro h
    have := add_pow_eq_add 0 (i + 1) a b (by rw [add_comm]; exact h)
    omega
  | i + 1, k + 1, a, b => by
    intro h
    have hi3 : 3 ∣ 3 ^ (i + 1) := dvd_pow_self 3 (by omega)
    have hk3 : 3 ∣ 3 ^ (k + 1) := dvd_pow_self 3 (by omega)
    have hsum : 3 ∣ 3 ^ a + 3 ^ b := by rw [← h]; exact dvd_add hi3 hk3
    rcases Nat.eq_zero_or_pos a with ha | ha
    · exfalso; subst ha
      rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb; norm_num at hsum
      · have := (Nat.dvd_add_left (dvd_pow_self 3 hb.ne')).1 hsum; norm_num at this
    · rcases Nat.eq_zero_or_pos b with hb | hb
      · exfalso; subst hb
        have := (Nat.dvd_add_right (dvd_pow_self 3 ha.ne')).1 hsum; norm_num at this
      · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
        obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        rw [pow_succ, pow_succ, pow_succ, pow_succ] at h
        have := add_pow_eq_add i k a' b' (by omega)
        omega

end Weights

end Jones1980
