import Surreal.Algebra.PellTwoDivisibility
import Surreal.Algebra.IntersectivePolynomialModular

/-!
# The three-equation system defining ordinary constants

The literal parameter-free system `odg:def:eq:system` and the algebraic
proof interface for `odg:def:thm:constants`. Its five witnesses use only
ring operations and integer numerals. The forward implication combines
Pell rigidity, the root obstruction, and constant-divisor rigidity; the
converse uses the proved divisible Pell coordinates and intersectivity.
-/

namespace Surreal.DiophantineConstants

open IntersectivePolynomial

noncomputable section

variable {R S O : Type*} [CommRing R] [CommRing S] [CommRing O]

/-- The three equations printed in the manuscript, with exactly five witnesses. -/
def System (x u v w s t : R) : Prop :=
  x * (u ^ 2 - 2 * v ^ 2 - 1) = 0 ∧
    x * (v - x * w) = 0 ∧ x * (v * s - value t) = 0

/-- The existential predicate Xi, with no parameters beyond integer numerals. -/
def Xi (x : R) : Prop := ∃ u v w s t : R, System x u v w s t

theorem xi_zero : Xi (0 : R) := by
  exact ⟨0, 0, 0, 0, 0, by simp [System]⟩

/-- Unital ring maps preserve the literal equations. -/
theorem System.map (φ : R →+* S) {x u v w s t : R} (h : System x u v w s t) :
    System (φ x) (φ u) (φ v) (φ w) (φ s) (φ t) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  have h₁ := congrArg φ h₁
  have h₂ := congrArg φ h₂
  have h₃ := congrArg φ h₃
  simpa only [System, map_mul, map_sub, map_pow, map_ofNat, map_one, map_zero, map_value] using
    And.intro h₁ (And.intro h₂ h₃)

/-- The existential predicate is preserved by every unital ring homomorphism. -/
theorem Xi.map (φ : R →+* S) {x : R} (h : Xi x) : Xi (φ x) := by
  obtain ⟨u, v, w, s, t, h⟩ := h
  exact ⟨φ u, φ v, φ w, φ s, φ t, h.map φ⟩

/-- The witnesses can use a Pell index at most m² and a residue 0 ≤ t < Y_k. -/
theorem bounded_system_witnesses (x : R) (m : ℤ) (hm : 0 < m)
    (hx : x ∣ (m : R)) :
    ∃ k : ℕ, ∃ w : R, ∃ s t : ℤ,
      1 ≤ k ∧ k ≤ m.toNat ^ 2 ∧ 0 ≤ t ∧ t < PellTwo.Y k ∧ 0 < PellTwo.Y k ∧
        System x (PellTwo.X k : R) (PellTwo.Y k : R) w (s : R) (t : R) := by
  obtain ⟨k, hk1, hkb, hk, hy⟩ := PellTwo.exists_bounded_divisible_coordinate m.toNat (by omega)
  have hd : m ∣ PellTwo.Y k := by simpa only [Int.toNat_of_nonneg hm.le] using hk
  have hxv : x ∣ (PellTwo.Y k : R) := hx.trans (map_dvd (Int.castRingHom R) hd)
  obtain ⟨w, hw⟩ := hxv
  obtain ⟨t, ht0, htlt, s, hs⟩ := exists_integer_root_mod_bounded (PellTwo.Y k).toNat (by omega)
  have he : value t = PellTwo.Y k * s := by
    simpa only [Int.toNat_of_nonneg hy.le] using hs
  have hp : (PellTwo.X k : R) ^ 2 - 2 * (PellTwo.Y k : R) ^ 2 = 1 := by
    have h := congrArg (Int.castRingHom R) (PellTwo.equation k)
    simp only [map_sub, map_pow, map_mul, map_ofNat, map_one] at h
    exact h
  have hv : (PellTwo.Y k : R) * (s : R) = value (t : R) := by
    have h := congrArg (Int.castRingHom R) he
    rw [map_value, map_mul] at h
    exact h.symm
  refine ⟨k, w, s, t, hk1, hkb, ht0, ?_, hy, ?_⟩
  · simpa only [Int.toNat_of_nonneg hy.le] using htlt
  · simp only [System, hp, ← hw, hv, sub_self, mul_zero, and_self]

/-- A positive ordinary integer in the principal ideal supplies all five witnesses. -/
theorem xi_of_positive_integer_multiple (x : R) (m : ℤ) (hm : 0 < m)
    (hx : x ∣ (m : R)) : Xi x := by
  obtain ⟨k, w, s, t, _, _, _, _, _, he⟩ := bounded_system_witnesses x m hm hx
  exact ⟨PellTwo.X k, PellTwo.Y k, w, s, t, he⟩

/-- Every ordinary integer has witnesses in the ordinary integer ring itself. -/
theorem integer_xi (x : ℤ) : Xi x := by
  by_cases hx : x = 0
  · subst x
    exact xi_zero
  exact xi_of_positive_integer_multiple x |x| (abs_pos.mpr hx) (self_dvd_abs x)

/-- Every ordinary Gaussian integer has witnesses in the ordinary Gaussian ring. -/
theorem gaussian_xi (x : GaussianInt) : Xi x := by
  by_cases hx : x = 0
  · subst x
    exact xi_zero
  exact xi_of_positive_integer_multiple x (Zsqrtd.norm x) (GaussianInt.norm_pos.mpr hx)
    ⟨star x, Zsqrtd.norm_eq_mul_conj x⟩

/-- The soundness argument needs only Pell constancy, no roots of Lambda, and the
fact that divisors of nonzero constants are constants. -/
theorem xi_iff_mem_range [IsDomain R] (ι : O →+* R)
    (hpell : ∀ u v : R, u ^ 2 - 2 * v ^ 2 = 1 → v ∈ ι.range)
    (hroot : ∀ t : R, value t ≠ 0)
    (hdivisor : ∀ x w : R, ∀ a : O, ι a ≠ 0 → x * w = ι a → x ∈ ι.range)
    (hordinary : ∀ a : O, Xi a) (x : R) : Xi x ↔ x ∈ ι.range := by
  constructor
  · rintro ⟨u, v, w, s, t, h₁, h₂, h₃⟩
    by_cases hx : x = 0
    · rw [hx]
      exact ι.range.zero_mem
    have hp : u ^ 2 - 2 * v ^ 2 = 1 :=
      sub_eq_zero.mp ((mul_eq_zero.mp h₁).resolve_left hx)
    have hw : v = x * w := sub_eq_zero.mp ((mul_eq_zero.mp h₂).resolve_left hx)
    have hs : v * s = value t := sub_eq_zero.mp ((mul_eq_zero.mp h₃).resolve_left hx)
    have hv : v ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hs
      exact hroot t hs.symm
    obtain ⟨a, ha⟩ := hpell u v hp
    exact hdivisor x w a (ha ▸ hv) (hw.symm.trans ha.symm)
  · rintro ⟨a, rfl⟩
    exact (hordinary a).map ι

end
end Surreal.DiophantineConstants
