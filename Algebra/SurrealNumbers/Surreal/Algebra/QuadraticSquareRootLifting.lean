import Surreal.Algebra.QuadraticModularLifting

/-!
# Lifting modular square roots

The prime-power prerequisites of `odg:def:lem:tailored`. Every integer
congruent to one modulo eight has square roots modulo all powers of two;
nonzero squares modulo an odd prime lift to all powers of that prime.
-/

namespace Surreal.QuadraticModularLifting

/-- A nonzero square modulo an odd prime lifts to every prime power. -/
theorem exists_square_root_odd_prime_power (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2)
    (d : ℤ) (hd0 : (d : ZMod p) ≠ 0) (hd : IsSquare (d : ZMod p)) (n : ℕ) :
    ∃ r : ℤ, (p : ℤ) ^ n ∣ r ^ 2 - d := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := hd
  have hr0 : r ≠ 0 := by intro hz; simp [hz] at hr; exact hd0 hr
  have hn2 : (2 : ZMod p) ≠ 0 := by
    intro h
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h))
  let s : ℤ := r.val
  have hs : (s : ZMod p) = r := by simp [s]
  have hroot : (p : ℤ) ∣ s ^ 2 + 0 * s + -d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hs, hr]
    ring
  have hder : ¬(p : ℤ) ∣ 2 * s + 0 := by
    intro h
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    push_cast at he
    rw [hs] at he
    exact mul_ne_zero hn2 hr0 (by simpa using he)
  obtain ⟨t, ht, _⟩ := exists_root_prime_power p hp 0 (-d) s hroot hder n
  exact ⟨t, by simpa only [zero_mul, add_zero, sub_eq_add_neg] using ht⟩

/-- Every radicand congruent to one modulo eight is a square modulo every power of two. -/
theorem exists_square_root_two_power (d : ℤ) (hd : d ≡ 1 [ZMOD 8]) (n : ℕ) :
    ∃ r : ℤ, (2 : ℤ) ^ n ∣ r ^ 2 - d := by
  have hdiv : (8 : ℤ) ∣ d - 1 := Int.modEq_iff_dvd.mp hd.symm
  obtain ⟨k, hk⟩ := hdiv
  have he : d = 1 + 8 * k := by omega
  obtain ⟨r, hr, _⟩ := exists_root_prime_power 2 (by decide) 1 (-2 * k) 0
    (by simp) (by norm_num) n
  refine ⟨2 * r + 1, ?_⟩
  have h : (2 * r + 1) ^ 2 - d = 4 * (r ^ 2 + 1 * r + -2 * k) := by rw [he]; ring
  rw [h]
  exact dvd_mul_of_dvd_right hr 4

end Surreal.QuadraticModularLifting
