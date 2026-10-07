import OAI.Combinatorics.Progressions.Polynomial.LowTaggedPolynomialCoordinates

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)] {X : Type*}

theorem normalizedTwistFrequencyPolynomial_low_rationalLiftCharacterTwist
    (M d : ℕ) (hM : 0 < M) (a : (Σ j, J j) → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℝ)
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (β : Fin (Fintype.card (LowTaggedIndex J d)) → ℤ) :
    (Real.fourierChar (MvPolynomial.eval u
      (normalizedTwistFrequencyPolynomial M (truncateTaggedFrequency d a) poly)) : ℂ) =
      rationalLiftCharacterTwist M (lowTaggedFrequency J d a) c
        (fun i => MvPolynomial.eval u (lowTaggedPolynomial J d poly i) - c i - (β i : ℝ))
        (fun i => (β i : ZMod M)) := by
  rw [normalizedTwistFrequencyPolynomial_low_eval J]
  symm
  simpa only [sub_add_cancel] using
    rationalLiftCharacterTwist_residual M hM (lowTaggedFrequency J d a) c
      (fun i => MvPolynomial.eval u (lowTaggedPolynomial J d poly i) - c i) β

theorem normalizedTwistFrequencyPolynomial_low_rationalLiftCharacterTwist_affine
    (M d : ℕ) (hM : 0 < M) (a : (Σ j, J j) → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (start : X → ℤ) (q : ℤ) (v : X → ℤ)
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (β : Fin (Fintype.card (LowTaggedIndex J d)) → ℤ) :
    (Real.fourierChar (MvPolynomial.eval (fun x => ((start x + q * v x : ℤ) : ℝ))
      (normalizedTwistFrequencyPolynomial M (truncateTaggedFrequency d a) poly)) : ℂ) =
      rationalLiftCharacterTwist M (lowTaggedFrequency J d a) c
        (fun i => MvPolynomial.eval (fun x => ((start x + q * v x : ℤ) : ℝ))
          (lowTaggedPolynomial J d poly i) - c i - (β i : ℝ))
        (fun i => (β i : ZMod M)) :=
  normalizedTwistFrequencyPolynomial_low_rationalLiftCharacterTwist J M d hM a poly
    (fun x => ((start x + q * v x : ℤ) : ℝ)) c β

end Erdos3.VectorPolynomial

end

end OAI
