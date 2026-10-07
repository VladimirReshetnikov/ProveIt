import Mathlib.Algebra.MvPolynomial.Derivation

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem polynomialDerivation_intertwine_of_X
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (E : Derivation R (MvPolynomial τ R) (MvPolynomial τ R))
    (hX : ∀ i, φ (D (X i)) = E (φ (X i))) (P : MvPolynomial σ R) :
    φ (D P) = E (φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have hC : φ (C c) = C c := φ.commutes c
      simp only [hC, MvPolynomial.derivation_C, map_zero]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hX, hP]

end Erdos3

end

end OAI
