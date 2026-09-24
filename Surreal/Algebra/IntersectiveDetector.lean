import Surreal.Algebra.AugmentationRootDetector
import Surreal.Algebra.IntersectivePolynomialModular

/-!
# The intersective constant-term detector

Specializes `odg:def:thm:augdetector` to the polynomial Lambda in
`odg:def:thm:detector` and `odg:def:eq:detector`. A square root of thirteen
in the coefficient field supplies its root; ordinary intersectivity and
root exclusion supply the remaining two hypotheses.
-/

namespace Surreal.IntersectivePolynomial

noncomputable section

variable {R S K H O : Type*} [CommRing R] [CommRing S]
  [Field K] [CommRing H] [Algebra K H] [CommRing O]

/-- Mapping the integer coefficients and evaluating gives the same literal formula. -/
theorem eval₂_mapped_polynomial (φ : O →+* R) (t : R) :
    (polynomial.map (Int.castRingHom O)).eval₂ φ t = value t := by
  simp [polynomial, value, map_ofNat]

/-- The literal parameter-free two-witness ring formula. -/
def Detects (a : R) : Prop := ∃ s t : R, a * s = value t

/-- Certificates are preserved by every unital ring homomorphism. -/
theorem Detects.map (φ : R →+* S) {a : R} (h : Detects a) : Detects (φ a) := by
  obtain ⟨s, t, he⟩ := h
  refine ⟨φ s, φ t, ?_⟩
  rw [← map_mul, he, map_value]

/-- The ordinary modular hypothesis in the exact form needed by the augmentation theorem. -/
theorem integer_modular_value (c : ℤ) (hc : c ≠ 0) :
    ∃ b d : ℤ, value b = c * d := by
  obtain ⟨b, hb⟩ := exists_integer_root_mod c.natAbs (Int.natAbs_pos.mpr hc)
  obtain ⟨d, hd⟩ := Int.natAbs_dvd.mp hb
  exact ⟨b, d, hd⟩

/-- The Gaussian modular hypothesis, with an ordinary integer evaluation point. -/
theorem gaussian_modular_value (c : GaussianInt) (hc : c ≠ 0) :
    ∃ b d : GaussianInt, value b = c * d := by
  obtain ⟨d, b, hb⟩ := gaussian_multiple_certificate c hc
  exact ⟨b, d, hb.symm⟩

/-- A common specialization for any embedded ordinary coefficient ring. -/
theorem pullback_detector_iff (ε : H →ₐ[K] K) (i : O →+* K)
    (hi : Function.Injective i) (hno : ∀ b : O, value b ≠ 0)
    (hmod : ∀ c : O, c ≠ 0 → ∃ b d : O, value b = c * d)
    (r : K) (hr : r ^ 2 = 13) (a : CoefficientPullback.subring ε.toRingHom i) :
    Detects a ↔ ε a.val ≠ 0 := by
  let f : Polynomial O := polynomial.map (Int.castRingHom O)
  have hno' (b : O) : f.eval b ≠ 0 := by
    simpa only [Polynomial.eval, f, eval₂_mapped_polynomial] using hno b
  have hmod' (c : O) (hc : c ≠ 0) : ∃ b d : O, f.eval b = c * d := by
    simpa only [Polynomial.eval, f, eval₂_mapped_polynomial] using hmod c hc
  have hr' : f.eval₂ i r = 0 := by simp only [f, eval₂_mapped_polynomial, value, hr, sub_self, zero_mul]
  simpa only [AugmentationRootDetector.Certificate, Detects, f, eval₂_mapped_polynomial] using
    AugmentationRootDetector.certificate_iff ε i hi f hno' r hr' hmod' a

/-- The detector for an integer coefficient pullback over any field containing sqrt(13). -/
theorem integer_pullback_detector_iff [CharZero K] (ε : H →ₐ[K] K)
    (r : K) (hr : r ^ 2 = 13)
    (a : CoefficientPullback.subring ε.toRingHom (Int.castRingHom K)) :
    Detects a ↔ ε a.val ≠ 0 :=
  pullback_detector_iff ε (Int.castRingHom K) Int.cast_injective integer_value_ne_zero
    integer_modular_value r hr a

/-- The analogous detector for an embedded Gaussian coefficient ring. -/
theorem gaussian_pullback_detector_iff (ε : H →ₐ[K] K)
    (i : GaussianInt →+* K) (hi : Function.Injective i) (r : K) (hr : r ^ 2 = 13)
    (a : CoefficientPullback.subring ε.toRingHom i) : Detects a ↔ ε a.val ≠ 0 :=
  pullback_detector_iff ε i hi gaussian_value_ne_zero gaussian_modular_value r hr a

end
end Surreal.IntersectivePolynomial
