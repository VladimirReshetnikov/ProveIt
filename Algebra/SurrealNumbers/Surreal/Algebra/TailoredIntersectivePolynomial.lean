import Surreal.Algebra.IntersectivePolynomialModular
import Surreal.Algebra.QuadraticSquareRootLifting
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Modular and root-exclusion properties of the tailored sextic

The local arithmetic and CRT steps of `odg:def:lem:tailored`. For primes
p ≡ 1 (mod 8) and q ≡ 1 (mod 8p), the source's sextic has a root modulo
every positive integer. It has no root in any field where p, q and pq
are nonsquares. Selecting such primes for each number field is separate.
-/

namespace Surreal.TailoredIntersectivePolynomial
open Polynomial
noncomputable section

/-- The integer sextic in the number-field construction. -/
def polynomial (p q : ℕ) : ℤ[X] :=
  (X ^ 2 - C (p : ℤ)) * (X ^ 2 - C (q : ℤ)) * (X ^ 2 - C ((p * q : ℕ) : ℤ))

/-- The same expression evaluated over an arbitrary commutative ring. -/
def value {R : Type*} [CommRing R] (p q : ℕ) (x : R) : R :=
  (x ^ 2 - (p : R)) * (x ^ 2 - (q : R)) * (x ^ 2 - ((p * q : ℕ) : R))

@[simp] theorem eval₂_polynomial {R : Type*} [CommRing R] (p q : ℕ) (x : R) :
    (polynomial p q).eval₂ (Int.castRingHom R) x = value p q x := by
  simp [polynomial, value]

@[simp] theorem map_value {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (p q : ℕ) (x : R) : φ (value p q x) = value p q (φ x) := by
  simp only [value, map_mul, map_sub, map_pow, map_natCast]

/-- The arithmetic progression conditions used in the manuscript. -/
def Admissible (p q : ℕ) : Prop := p.Prime ∧ q.Prime ∧ p % 8 = 1 ∧ q % (8 * p) = 1

/-- The second prime is one modulo the first and one modulo eight. -/
theorem admissible_congruences {p q : ℕ} (h : Admissible p q) :
    q % p = 1 ∧ q % 8 = 1 := by
  have hp := h.1.two_le
  constructor
  · have he := Nat.mod_mod_of_dvd q (dvd_mul_left p 8)
    rw [h.2.2.2, Nat.mod_eq_of_lt (by omega : 1 < p)] at he
    exact he.symm
  · have he := Nat.mod_mod_of_dvd q (dvd_mul_right 8 p)
    rw [h.2.2.2] at he
    exact he.symm

/-- In particular the two primes are distinct and both odd. -/
theorem admissible_distinct_odd {p q : ℕ} (h : Admissible p q) :
    p ≠ q ∧ p ≠ 2 ∧ q ≠ 2 := by
  obtain ⟨hqp, hq8⟩ := admissible_congruences h
  have hp8 := h.2.2.1
  refine ⟨?_, by omega, by omega⟩
  intro he
  rw [he, Nat.mod_self] at hqp
  omega

/-- At every prime, one radicand is a nonzero square; reciprocity handles the prime q. -/
theorem exists_square_radicand {p q : ℕ} (h : Admissible p q) (l : ℕ) (hl : l.Prime) :
    ∃ d : ℕ, (d = p ∨ d = q ∨ d = p * q) ∧
      (d : ZMod l) ≠ 0 ∧ IsSquare (d : ZMod l) := by
  letI : Fact p.Prime := ⟨h.1⟩
  letI : Fact q.Prime := ⟨h.2.1⟩
  letI : Fact l.Prime := ⟨hl⟩
  obtain ⟨hpq, _, hq2⟩ := admissible_distinct_odd h
  obtain ⟨hqp, _⟩ := admissible_congruences h
  have hqcast : (q : ZMod p) = 1 := by
    rw [← ZMod.natCast_mod q p, hqp, Nat.cast_one]
  have hqsq : IsSquare (q : ZMod p) := by rw [hqcast]; exact ⟨1, by simp⟩
  by_cases hlp : l = p
  · subst l
    exact ⟨q, Or.inr (Or.inl rfl), ZMod.prime_ne_zero p q hpq, hqsq⟩
  by_cases hlq : l = q
  · subst l
    have hp4 : p % 4 = 1 := by have hp8 := h.2.2.1; omega
    exact ⟨p, Or.inl rfl, ZMod.prime_ne_zero q p hpq.symm,
      (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one hp4 hq2).mp hqsq⟩
  have hp0 : (p : ZMod l) ≠ 0 := ZMod.prime_ne_zero l p hlp
  have hq0 : (q : ZMod l) ≠ 0 := ZMod.prime_ne_zero l q hlq
  by_cases hps : IsSquare (p : ZMod l)
  · exact ⟨p, Or.inl rfl, hp0, hps⟩
  by_cases hqs : IsSquare (q : ZMod l)
  · exact ⟨q, Or.inr (Or.inl rfl), hq0, hqs⟩
  refine ⟨p * q, Or.inr (Or.inr rfl), ?_, ?_⟩
  · simpa only [Nat.cast_mul] using mul_ne_zero hp0 hq0
  · simpa only [Nat.cast_mul] using
      IntersectivePolynomial.finiteField_nonsquares_mul _ _ hp0 hq0 hps hqs

/-- Each prime power admits an ordinary integer root of the tailored sextic. -/
theorem exists_root_prime_power {p q : ℕ} (h : Admissible p q)
    (l : ℕ) (hl : l.Prime) (n : ℕ) : ∃ r : ℤ, (l : ℤ) ^ n ∣ value p q r := by
  by_cases hl2 : l = 2
  · subst l
    have hp8 : (p : ℤ) ≡ 1 [ZMOD 8] := by
      exact Int.natCast_modEq_iff.mpr h.2.2.1
    obtain ⟨r, hr⟩ := QuadraticModularLifting.exists_square_root_two_power p hp8 n
    exact ⟨r, dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hr _) _⟩
  · obtain ⟨d, hd, hd0, hds⟩ := exists_square_radicand h l hl
    obtain ⟨r, hr⟩ := QuadraticModularLifting.exists_square_root_odd_prime_power l hl hl2 d
      (by simpa only [Int.cast_natCast] using hd0) (by simpa only [Int.cast_natCast] using hds) n
    refine ⟨r, ?_⟩
    rcases hd with rfl | rfl | rfl
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hr _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hr _) _
    · exact dvd_mul_of_dvd_right hr _

/-- CRT combines the local roots into a root in every nonzero residue ring. -/
theorem exists_zmod_root {p q : ℕ} (h : Admissible p q) (m : ℕ) (hm : m ≠ 0) :
    ∃ x : ZMod m, value p q x = 0 := by
  have aux : ∀ m : ℕ, m ≠ 0 → ∃ x : ZMod m, value p q x = 0 := by
    apply Nat.recOnPrimeCoprime
    · intro hz
      exact (hz rfl).elim
    · intro l n hl _
      obtain ⟨r, hr⟩ := exists_root_prime_power h l hl n
      refine ⟨(r : ZMod (l ^ n)), ?_⟩
      have he : ((value p q r : ℤ) : ZMod (l ^ n)) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa only [Nat.cast_pow] using hr)
      change (Int.castRingHom (ZMod (l ^ n))) (value p q r) = 0 at he
      rwa [map_value] at he
    · intro a b ha hb hab hroota hrootb _
      obtain ⟨x, hx⟩ := hroota (by omega)
      obtain ⟨y, hy⟩ := hrootb (by omega)
      let e := ZMod.chineseRemainder hab
      refine ⟨e.symm (x, y), ?_⟩
      apply e.injective
      change e.toRingHom (value p q (e.symm (x, y))) = e.toRingHom 0
      rw [map_value, map_zero]
      change value p q (e (e.symm (x, y))) = 0
      rw [e.apply_symm_apply]
      exact Prod.ext hx hy
  exact aux m hm

/-- The modular root can be chosen in the interval from zero to the modulus minus one. -/
theorem exists_integer_root_mod_bounded {p q : ℕ} (h : Admissible p q) (m : ℕ) (hm : 0 < m) :
    ∃ r : ℤ, 0 ≤ r ∧ r < (m : ℤ) ∧ (m : ℤ) ∣ value p q r := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨x, hx⟩ := exists_zmod_root h m (Nat.ne_of_gt hm)
  refine ⟨x.val, Int.natCast_nonneg _, by exact_mod_cast x.val_lt, ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  change (Int.castRingHom (ZMod m)) (value p q (x.val : ℤ)) = 0
  rw [map_value]
  change value p q (((x.val : ℕ) : ℤ) : ZMod m) = 0
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hx

/-- Nonsquareness of the three radicands excludes all roots, without ordering assumptions. -/
theorem value_ne_zero {K : Type*} [Field K] (p q : ℕ)
    (hp : ¬IsSquare (p : K)) (hq : ¬IsSquare (q : K))
    (hpq : ¬IsSquare ((p * q : ℕ) : K)) (x : K) : value p q x ≠ 0 := by
  intro hz
  rcases mul_eq_zero.mp hz with hab | hc
  · rcases mul_eq_zero.mp hab with ha | hb
    · exact hp ⟨x, by simpa only [pow_two] using (sub_eq_zero.mp ha).symm⟩
    · exact hq ⟨x, by simpa only [pow_two] using (sub_eq_zero.mp hb).symm⟩
  · exact hpq ⟨x, by simpa only [pow_two] using (sub_eq_zero.mp hc).symm⟩

end
end Surreal.TailoredIntersectivePolynomial
