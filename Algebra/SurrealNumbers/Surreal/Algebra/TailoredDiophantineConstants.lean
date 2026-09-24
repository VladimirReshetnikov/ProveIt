import Surreal.Algebra.TailoredIntersectivePolynomial
import Surreal.Algebra.PellTwoDivisibility

/-!
# Ordinary witnesses for the tailored constant-definition system

The algebraic implication in `odg:def:thm:numberfield`: any admissible prime
pair supplies the five witnesses for every element of a number-field subring.
Soundness uses only Pell rigidity, root exclusion and constant-divisor rigidity.
-/

namespace Surreal.TailoredDiophantineConstants
open TailoredIntersectivePolynomial

variable {R S O : Type*} [CommRing R] [CommRing S] [CommRing O]

/-- The source's three equations with its tailored sextic. -/
def System (p q : ℕ) (x u v w s t : R) : Prop :=
  x * (u ^ 2 - 2 * v ^ 2 - 1) = 0 ∧
    x * (v - x * w) = 0 ∧ x * (v * s - value p q t) = 0

/-- The tailored constant predicate has exactly five existential witnesses. -/
def Xi (p q : ℕ) (x : R) : Prop := ∃ u v w s t : R, System p q x u v w s t

theorem xi_zero (p q : ℕ) : Xi p q (0 : R) := ⟨0, 0, 0, 0, 0, by simp [System]⟩

/-- Unital ring maps preserve the tailored equations. -/
theorem System.map {p q : ℕ} (φ : R →+* S) {x u v w s t : R}
    (h : System p q x u v w s t) : System p q (φ x) (φ u) (φ v) (φ w) (φ s) (φ t) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  have h₁ := congrArg φ h₁
  have h₂ := congrArg φ h₂
  have h₃ := congrArg φ h₃
  simpa only [System, map_mul, map_sub, map_pow, map_ofNat, map_one, map_zero, map_value] using
    And.intro h₁ (And.intro h₂ h₃)

/-- Existential witnesses transfer along every unital ring map. -/
theorem Xi.map {p q : ℕ} (φ : R →+* S) {x : R} (h : Xi p q x) : Xi p q (φ x) := by
  obtain ⟨u, v, w, s, t, h⟩ := h
  exact ⟨φ u, φ v, φ w, φ s, φ t, h.map φ⟩

/-- A positive integer multiple supplies all five witnesses, with a bounded Pell index
and a least nonnegative residue for the sextic argument. -/
theorem bounded_system_witnesses {p q : ℕ} (h : Admissible p q)
    (x : R) (m : ℤ) (hm : 0 < m) (hx : x ∣ (m : R)) :
    ∃ k : ℕ, ∃ w : R, ∃ s t : ℤ,
      1 ≤ k ∧ k ≤ m.toNat ^ 2 ∧ 0 ≤ t ∧ t < PellTwo.Y k ∧ 0 < PellTwo.Y k ∧
        System p q x (PellTwo.X k : R) (PellTwo.Y k : R) w (s : R) (t : R) := by
  obtain ⟨k, hk1, hkb, hk, hy⟩ := PellTwo.exists_bounded_divisible_coordinate m.toNat (by omega)
  have hd : m ∣ PellTwo.Y k := by simpa only [Int.toNat_of_nonneg hm.le] using hk
  have hxv : x ∣ (PellTwo.Y k : R) := hx.trans (map_dvd (Int.castRingHom R) hd)
  obtain ⟨w, hw⟩ := hxv
  obtain ⟨t, ht0, htlt, s, hs⟩ := exists_integer_root_mod_bounded h (PellTwo.Y k).toNat (by omega)
  have he : value p q t = PellTwo.Y k * s := by
    simpa only [Int.toNat_of_nonneg hy.le] using hs
  have hpell : (PellTwo.X k : R) ^ 2 - 2 * (PellTwo.Y k : R) ^ 2 = 1 := by
    have hpell := congrArg (Int.castRingHom R) (PellTwo.equation k)
    simp only [map_sub, map_pow, map_mul, map_ofNat, map_one] at hpell
    exact hpell
  have hv : (PellTwo.Y k : R) * (s : R) = value p q (t : R) := by
    have hv := congrArg (Int.castRingHom R) he
    rw [map_value, map_mul] at hv
    exact hv.symm
  refine ⟨k, w, s, t, hk1, hkb, ht0, ?_, hy, ?_⟩
  · simpa only [Int.toNat_of_nonneg hy.le] using htlt
  · simp only [System, hpell, ← hw, hv, sub_self, mul_zero, and_self]

/-- Positive integer divisibility suffices for the tailored predicate. -/
theorem xi_of_positive_integer_multiple {p q : ℕ} (h : Admissible p q)
    (x : R) (m : ℤ) (hm : 0 < m) (hx : x ∣ (m : R)) : Xi p q x := by
  obtain ⟨k, w, s, t, _, _, _, _, _, he⟩ := bounded_system_witnesses h x m hm hx
  exact ⟨PellTwo.X k, PellTwo.Y k, w, s, t, he⟩

/-- Algebraicity suffices for ordinary witnesses; integrality is unnecessary. -/
theorem xi_of_isAlgebraic [IsDomain R] {p q : ℕ} (h : Admissible p q)
    (x : R) (hx : IsAlgebraic ℤ x) : Xi p q x := by
  by_cases hz : x = 0
  · subst x
    exact xi_zero p q
  obtain ⟨m, hm, hd⟩ := IntegerPrincipalMultiples.exists_positive_integer_multiple x hx
    (mem_nonZeroDivisors_of_ne_zero hz)
  exact xi_of_positive_integer_multiple h x m hm hd

/-- All subrings of number fields have ordinary witnesses, including nonintegral subrings. -/
theorem numberField_subring_xi {K : Type*} [Field K] [NumberField K]
    {p q : ℕ} (h : Admissible p q) (o : Subring K) (x : o) : Xi p q x := by
  by_cases hz : x = 0
  · subst x
    exact xi_zero p q
  obtain ⟨m, hm, hd⟩ := IntegerPrincipalMultiples.subring_exists_positive_integer_multiple o x hz
  exact xi_of_positive_integer_multiple h x m hm hd

/-- Pell constancy, root exclusion and rigidity of constant divisors prove soundness. -/
theorem xi_iff_mem_range [IsDomain R] (p q : ℕ) (ι : O →+* R)
    (hpell : ∀ u v : R, u ^ 2 - 2 * v ^ 2 = 1 → v ∈ ι.range)
    (hroot : ∀ t : R, value p q t ≠ 0)
    (hdivisor : ∀ x w : R, ∀ a : O, ι a ≠ 0 → x * w = ι a → x ∈ ι.range)
    (hordinary : ∀ a : O, Xi p q a) (x : R) : Xi p q x ↔ x ∈ ι.range := by
  constructor
  · rintro ⟨u, v, w, s, t, h₁, h₂, h₃⟩
    by_cases hx : x = 0
    · rw [hx]
      exact ι.range.zero_mem
    have hp : u ^ 2 - 2 * v ^ 2 = 1 :=
      sub_eq_zero.mp ((mul_eq_zero.mp h₁).resolve_left hx)
    have hw : v = x * w := sub_eq_zero.mp ((mul_eq_zero.mp h₂).resolve_left hx)
    have hs : v * s = value p q t := sub_eq_zero.mp ((mul_eq_zero.mp h₃).resolve_left hx)
    have hv : v ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hs
      exact hroot t hs.symm
    obtain ⟨a, ha⟩ := hpell u v hp
    exact hdivisor x w a (ha ▸ hv) (hw.symm.trans ha.symm)
  · rintro ⟨a, rfl⟩
    exact (hordinary a).map ι

end Surreal.TailoredDiophantineConstants
