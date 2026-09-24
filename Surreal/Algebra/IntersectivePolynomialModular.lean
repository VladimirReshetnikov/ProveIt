import Surreal.Algebra.IntersectivePolynomial
import Surreal.Algebra.QuadraticModularLifting
import Surreal.Algebra.IntegerPrincipalMultiples
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Roots of Lambda modulo every positive integer

The remaining clauses (i) and (iii) of `odg:def:prop:intersective`.
Quadratic characters choose a nonsingular factor at every odd prime;
the polynomial x² + x − 4 handles the prime 2. Integer lifting and the
Chinese remainder theorem give roots for every positive modulus.
-/

namespace Surreal.IntersectivePolynomial

noncomputable section

/-- Two nonsquares in a finite field have square product. -/
theorem finiteField_nonsquares_mul {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) (hna : ¬IsSquare a) (hnb : ¬IsSquare b) :
    IsSquare (a * b) := by
  apply (quadraticChar_one_iff_isSquare (mul_ne_zero ha hb)).mp
  rw [map_mul, quadraticChar_neg_one_iff_not_isSquare.mpr hna,
    quadraticChar_neg_one_iff_not_isSquare.mpr hnb]
  norm_num

/-- At each prime, one of the three radicands is a nonzero square. -/
theorem exists_square_radicand (p : ℕ) (hp : p.Prime) :
    ∃ d : ℤ, (d = 13 ∨ d = 17 ∨ d = 221) ∧
      (d : ZMod p) ≠ 0 ∧ IsSquare (d : ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases h13 : p = 13
  · subst p
    exact ⟨17, Or.inr (Or.inl rfl), by decide, 2, by decide +revert⟩
  by_cases h17 : p = 17
  · subst p
    exact ⟨13, Or.inl rfl, by decide, 8, by decide +revert⟩
  have hn13 : (13 : ZMod p) ≠ 0 := by
    intro h
    exact h13 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13)).mp
      ((ZMod.natCast_eq_zero_iff 13 p).mp h))
  have hn17 : (17 : ZMod p) ≠ 0 := by
    intro h
    exact h17 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 17)).mp
      ((ZMod.natCast_eq_zero_iff 17 p).mp h))
  by_cases hs13 : IsSquare (13 : ZMod p)
  · exact ⟨13, Or.inl rfl, by simpa using hn13, by simpa using hs13⟩
  by_cases hs17 : IsSquare (17 : ZMod p)
  · exact ⟨17, Or.inr (Or.inl rfl), by simpa using hn17, by simpa using hs17⟩
  refine ⟨221, Or.inr (Or.inr rfl), ?_, ?_⟩
  · convert mul_ne_zero hn13 hn17 using 1; norm_num
  · convert finiteField_nonsquares_mul (13 : ZMod p) 17 hn13 hn17 hs13 hs17 using 1
    norm_num

/-- The radicand 17 has a square root modulo every power of 2. -/
theorem exists_square_root_seventeen_two_power (n : ℕ) :
    ∃ r : ℤ, (2 : ℤ) ^ n ∣ r ^ 2 - 17 := by
  obtain ⟨r, hr, _⟩ := QuadraticModularLifting.exists_root_prime_power
    2 (by decide) 1 (-4) 0 (by norm_num) (by norm_num) n
  refine ⟨2 * r + 1, ?_⟩
  have he : (2 * r + 1) ^ 2 - 17 = 4 * (r ^ 2 + 1 * r + -4) := by ring
  rw [he]
  exact dvd_mul_of_dvd_right hr 4

/-- Every odd prime power has a square root of one of the three radicands. -/
theorem exists_square_root_odd_prime_power (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (n : ℕ) :
    ∃ d r : ℤ, (d = 13 ∨ d = 17 ∨ d = 221) ∧ (p : ℤ) ^ n ∣ r ^ 2 - d := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, hd0, r, hr⟩ := exists_square_radicand p hp
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
  obtain ⟨t, ht, _⟩ := QuadraticModularLifting.exists_root_prime_power p hp 0 (-d) s hroot hder n
  exact ⟨d, t, hd, by simpa only [zero_mul, add_zero, sub_eq_add_neg] using ht⟩

/-- Lambda has an integer root modulo every prime power. -/
theorem exists_root_prime_power (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ∃ r : ℤ, (p : ℤ) ^ n ∣ value r := by
  by_cases h2 : p = 2
  · subst p
    obtain ⟨r, hr⟩ := exists_square_root_seventeen_two_power n
    exact ⟨r, dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hr _) _⟩
  · obtain ⟨d, r, hd, hr⟩ := exists_square_root_odd_prime_power p hp h2 n
    refine ⟨r, ?_⟩
    rcases hd with rfl | rfl | rfl
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hr _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hr _) _
    · exact dvd_mul_of_dvd_right hr _

/-- The native residue ring has a root of Lambda at every nonzero modulus. -/
theorem exists_zmod_root (m : ℕ) (hm : m ≠ 0) : ∃ x : ZMod m, value x = 0 := by
  have aux : ∀ m : ℕ, m ≠ 0 → ∃ x : ZMod m, value x = 0 := by
    apply Nat.recOnPrimeCoprime
    · intro h
      exact (h rfl).elim
    · intro p n hp _
      obtain ⟨r, hr⟩ := exists_root_prime_power p hp n
      refine ⟨(r : ZMod (p ^ n)), ?_⟩
      have he : ((value r : ℤ) : ZMod (p ^ n)) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa only [Nat.cast_pow] using hr)
      change (Int.castRingHom (ZMod (p ^ n))) (value r) = 0 at he
      rw [map_value] at he
      exact he
    · intro a b ha hb hab hroota hrootb _
      obtain ⟨x, hx⟩ := hroota (by omega)
      obtain ⟨y, hy⟩ := hrootb (by omega)
      let e := ZMod.chineseRemainder hab
      refine ⟨e.symm (x, y), ?_⟩
      apply e.injective
      change e.toRingHom (value (e.symm (x, y))) = e.toRingHom 0
      rw [map_value, map_zero]
      change value (e (e.symm (x, y))) = 0
      rw [e.apply_symm_apply]
      exact Prod.ext hx hy
  exact aux m hm

/-- An intersective root can be chosen as the least nonnegative residue representative. -/
theorem exists_integer_root_mod_bounded (m : ℕ) (hm : 0 < m) :
    ∃ r : ℤ, 0 ≤ r ∧ r < (m : ℤ) ∧ (m : ℤ) ∣ value r := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨x, hx⟩ := exists_zmod_root m (Nat.ne_of_gt hm)
  refine ⟨x.val, Int.natCast_nonneg _, by exact_mod_cast x.val_lt, ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  change (Int.castRingHom (ZMod m)) (value (x.val : ℤ)) = 0
  rw [map_value]
  change value (((x.val : ℕ) : ℤ) : ZMod m) = 0
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hx

/-- The full intersectivity assertion, with an ordinary integer witness. -/
theorem exists_integer_root_mod (m : ℕ) (hm : 0 < m) :
    ∃ r : ℤ, (m : ℤ) ∣ value r := by
  obtain ⟨r, _, _, hr⟩ := exists_integer_root_mod_bounded m hm
  exact ⟨r, hr⟩

/-- Every nonzero Gaussian integer divides a value of Lambda at an ordinary integer. -/
theorem gaussian_multiple_certificate (v : GaussianInt) (hv : v ≠ 0) :
    ∃ s : GaussianInt, ∃ t : ℤ, v * s = value (t : GaussianInt) := by
  have hn := GaussianInt.norm_pos.mpr hv
  obtain ⟨t, q, hq⟩ := exists_integer_root_mod (Zsqrtd.norm v).toNat (by omega)
  have he : value t = Zsqrtd.norm v * q := by
    simpa only [Int.toNat_of_nonneg hn.le] using hq
  refine ⟨star v * (q : GaussianInt), t, ?_⟩
  rw [← mul_assoc, ← Zsqrtd.norm_eq_mul_conj]
  have h := congrArg (Int.castRingHom GaussianInt) he
  rw [map_value, map_mul] at h
  exact h.symm

/-- Among ordinary Gaussian integers, this existential equation detects exactly the nonzero ones. -/
theorem gaussian_nonzero_iff_multiple_certificate (v : GaussianInt) :
    v ≠ 0 ↔ ∃ s : GaussianInt, ∃ t : ℤ, v * s = value (t : GaussianInt) := by
  constructor
  · exact gaussian_multiple_certificate v
  · rintro ⟨s, t, he⟩ hv
    rw [hv, zero_mul] at he
    exact gaussian_value_ne_zero (t : GaussianInt) he.symm

end
end Surreal.IntersectivePolynomial
