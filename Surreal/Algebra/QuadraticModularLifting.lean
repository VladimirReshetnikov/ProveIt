import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Lifting simple quadratic roots modulo prime powers

An elementary integer lifting step for `odg:def:prop:intersective` (i).
The derivative condition works at every prime, including 2, so it applies
both to odd-prime square roots and to x² + x − 4 at the prime 2.
-/

namespace Surreal.QuadraticModularLifting

noncomputable section

/-- A simple integer root of a monic quadratic modulo a prime lifts to every prime power.
The derivative remains nonzero modulo the prime throughout the construction. -/
theorem exists_root_prime_power (p : ℕ) (hp : p.Prime) (b c r₀ : ℤ)
    (hroot : (p : ℤ) ∣ r₀ ^ 2 + b * r₀ + c)
    (hder : ¬(p : ℤ) ∣ 2 * r₀ + b) (n : ℕ) :
    ∃ r : ℤ, (p : ℤ) ^ n ∣ r ^ 2 + b * r + c ∧ ¬(p : ℤ) ∣ 2 * r + b := by
  letI : Fact p.Prime := ⟨hp⟩
  have aux : ∀ k : ℕ, ∃ r : ℤ,
      (p : ℤ) ^ (k + 1) ∣ r ^ 2 + b * r + c ∧ ¬(p : ℤ) ∣ 2 * r + b := by
    intro k
    induction k with
    | zero => exact ⟨r₀, by simpa using hroot, hder⟩
    | succ k ih =>
      obtain ⟨r, ⟨q, hq⟩, hd⟩ := ih
      let t : ℤ := ((-(q : ZMod p) / ((2 * r + b : ℤ) : ZMod p)).val : ℕ)
      have hd' : (((2 * r + b : ℤ) : ZMod p)) ≠ 0 := by
        intro hzero
        exact hd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero)
      have ht : (p : ℤ) ∣ q + (2 * r + b) * t := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        simp only [Int.cast_add, Int.cast_mul, t, Int.cast_natCast, ZMod.natCast_zmod_val]
        have hd'' : (2 * (r : ZMod p) + (b : ZMod p)) ≠ 0 := by
          simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using hd'
        norm_num only [Int.cast_ofNat]
        rw [mul_div_cancel₀ _ hd'']
        ring
      have hpow : (p : ℤ) ∣ (p : ℤ) ^ (k + 1) := dvd_pow_self _ (by omega)
      have hm : (p : ℤ) ∣ q + (2 * r + b) * t + (p : ℤ) ^ (k + 1) * t ^ 2 :=
        dvd_add ht (dvd_mul_of_dvd_left hpow _)
      obtain ⟨s, hs⟩ := hm
      refine ⟨r + (p : ℤ) ^ (k + 1) * t, ⟨s, ?_⟩, ?_⟩
      · rw [show k + 1 + 1 = (k + 1) + 1 by rfl, pow_succ]
        linear_combination hq + (p : ℤ) ^ (k + 1) * hs
      · intro hn
        apply hd
        have he : (p : ℤ) ∣ 2 * ((p : ℤ) ^ (k + 1) * t) :=
          dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hpow t) 2
        have hval : 2 * (r + (p : ℤ) ^ (k + 1) * t) + b -
            2 * ((p : ℤ) ^ (k + 1) * t) = 2 * r + b := by ring
        rw [← hval]
        exact dvd_sub hn he
  cases n with
  | zero => exact ⟨r₀, by simp, hder⟩
  | succ n => exact aux n

end
end Surreal.QuadraticModularLifting
