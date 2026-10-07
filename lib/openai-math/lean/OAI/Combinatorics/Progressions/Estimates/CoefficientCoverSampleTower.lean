import OAI.Combinatorics.Progressions.Lattices.AffineCoefficientCoverTilt

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem affineCoefficientCoverSample_product_projection
    {X K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (a d : ℕ) (ha : 0 < a) (b : Option K → X → ℝ) :
    quotientIntegerCover (coefficientIntegerLattice U) a
      (affineCoefficientCoverSample U p hm (a * d) b) =
      affineCoefficientCoverSample U p hm d b := by
  have ha0 : (a : ℝ) ≠ 0 := (Nat.cast_pos.mpr ha).ne'
  simp only [affineCoefficientCoverSample, quotientIntegerCover_mk, smul_smul, Nat.cast_mul,
    mul_inv_rev]
  congr 1
  congr 1
  calc
    (a : ℝ) * ((d : ℝ)⁻¹ * (a : ℝ)⁻¹) = (d : ℝ)⁻¹ * ((a : ℝ) * (a : ℝ)⁻¹) := by ring
    _ = (d : ℝ)⁻¹ := by rw [mul_inv_cancel₀ ha0, mul_one]

theorem affineCoefficientCoverSample_divisor_projection
    {X K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (D d : ℕ) (hD : 0 < D) (hdiv : d ∣ D) (b : Option K → X → ℝ) :
    quotientIntegerCover (coefficientIntegerLattice U) (D / d)
      (affineCoefficientCoverSample U p hm D b) =
      affineCoefficientCoverSample U p hm d b := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdiv hD
  have ha : 0 < D / d := Nat.div_pos (Nat.le_of_dvd hD hdiv) hd
  have h := affineCoefficientCoverSample_product_projection U p hm (D / d) d ha b
  simpa only [Nat.div_mul_cancel hdiv] using h

end Erdos3.VectorPolynomial

end

end OAI
