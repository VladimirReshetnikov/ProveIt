import Surreal.Algebra.AugmentationRootDetector
import Surreal.Algebra.TailoredDiophantineConstants

/-!
# The tailored number-field constant-term detector

The detector clause of `odg:def:thm:numberfield`. Intersectivity and a
positive integer in each nonzero principal ideal provide the ordinary
modular hypothesis. Any root of the sextic in the coefficient field
then gives the detector on the full augmentation pullback.
-/

namespace Surreal.TailoredIntersectivePolynomial
noncomputable section

variable {R S K H O : Type*} [CommRing R] [CommRing S]
    [Field K] [CommRing H] [Algebra K H] [CommRing O]

/-- Evaluating the coefficient-mapped sextic gives the literal tailored value. -/
theorem eval₂_mapped_polynomial (p q : ℕ) (φ : O →+* R) (t : R) :
    ((polynomial p q).map (Int.castRingHom O)).eval₂ φ t = value p q t := by
  simp [polynomial, value]

/-- The tailored two-witness detector, using only ring operations and integer numerals. -/
def Detects (p q : ℕ) (a : R) : Prop := ∃ s t : R, a * s = value p q t

/-- Unital ring maps preserve certificates. -/
theorem Detects.map {p q : ℕ} (φ : R →+* S) {a : R} (h : Detects p q a) :
    Detects p q (φ a) := by
  obtain ⟨s, t, he⟩ := h
  exact ⟨φ s, φ t, by rw [← map_mul, he, map_value]⟩

/-- A positive integer multiple and intersectivity give a certificate at an integer argument. -/
theorem modular_value_of_integer_multiple {p q : ℕ} (h : Admissible p q)
    (c : O) (m : ℤ) (hm : 0 < m) (hc : c ∣ (m : O)) :
    ∃ b : ℤ, ∃ d : O, value p q (b : O) = c * d := by
  obtain ⟨b, _, _, hb⟩ := exists_integer_root_mod_bounded h m.toNat (by omega)
  have hd : m ∣ value p q b := by simpa only [Int.toNat_of_nonneg hm.le] using hb
  have hmapped : (m : O) ∣ value p q (b : O) := by
    have he := map_dvd (Int.castRingHom O) hd
    rw [map_value] at he
    exact he
  obtain ⟨d, he⟩ := hc.trans hmapped
  exact ⟨b, d, he⟩

/-- Every nonzero element of a number-field subring divides a tailored value in that subring. -/
theorem numberField_subring_modular_value {F : Type*} [Field F] [NumberField F]
    {p q : ℕ} (h : Admissible p q) (o : Subring F) (c : o) (hc : c ≠ 0) :
    ∃ b d : o, value p q b = c * d := by
  obtain ⟨m, hm, hd⟩ := IntegerPrincipalMultiples.subring_exists_positive_integer_multiple o c hc
  obtain ⟨b, d, he⟩ := modular_value_of_integer_multiple h c m hm hd
  exact ⟨b, d, he⟩

/-- Root exclusion, ordinary modular values and any coefficient-field root suffice. -/
theorem pullback_detector_iff (p q : ℕ) (ε : H →ₐ[K] K) (i : O →+* K)
    (hi : Function.Injective i) (hno : ∀ b : O, value p q b ≠ 0)
    (hmod : ∀ c : O, c ≠ 0 → ∃ b d : O, value p q b = c * d)
    (r : K) (hr : value p q r = 0) (a : CoefficientPullback.subring ε.toRingHom i) :
    Detects p q a ↔ ε a.val ≠ 0 := by
  let f : Polynomial O := (polynomial p q).map (Int.castRingHom O)
  have hno' (b : O) : f.eval b ≠ 0 := by
    simpa only [Polynomial.eval, f, eval₂_mapped_polynomial] using hno b
  have hmod' (c : O) (hc : c ≠ 0) : ∃ b d : O, f.eval b = c * d := by
    simpa only [Polynomial.eval, f, eval₂_mapped_polynomial] using hmod c hc
  have hr' : f.eval₂ i r = 0 := by simpa only [f, eval₂_mapped_polynomial] using hr
  simpa only [AugmentationRootDetector.Certificate, Detects, f, eval₂_mapped_polynomial] using
    AugmentationRootDetector.certificate_iff ε i hi f hno' r hr' hmod' a

end
end Surreal.TailoredIntersectivePolynomial
