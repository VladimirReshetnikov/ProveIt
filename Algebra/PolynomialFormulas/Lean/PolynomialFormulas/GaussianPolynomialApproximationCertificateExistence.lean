import PolynomialFormulas.GaussianPolynomialApproximationSearch
import PolynomialFormulas.GaussianPolynomialApproximationFactors
import PolynomialFormulas.GaussianPolynomialApproximationExistence

/-!
# Termination certificate for the executable quartic root search

Every monic Gaussian-rational polynomial of degree at most four has a valid
finite rational certificate.  The proof factors it into four separable layers
and uses density of Gaussian rationals around the simple roots of each layer.
This theorem is passed to `Nat.find`; it is proof-only and is erased from the
compiled search.
-/

namespace LeanProofs.PolynomialFormulas

namespace GaussianPolynomialApproximationCertificateExistence

open GaussianPolynomialApproximationCore
open GaussianPolynomialApproximationCore.QPoly
open GaussianPolynomialApproximationSearch
open GaussianPolynomialApproximationFactors
open GaussianPolynomialApproximationExistence

theorem toPolynomial_factorProduct (raw : RawCertificate) :
    toPolynomial (factorProduct raw) =
      toPolynomial (raw.factors 0) * toPolynomial (raw.factors 1) *
        toPolynomial (raw.factors 2) * toPolynomial (raw.factors 3) := by
  simp [factorProduct, mul_assoc]

theorem productMatches_of_toPolynomial_eq {p : QPoly4} {raw : RawCertificate}
    (h : toPolynomial (factorProduct raw) = toPolynomial p) :
    ProductMatches p raw := by
  intro i
  have hi := congrArg (fun q : Polynomial GaussianRat => q.coeff i) h
  simpa using hi

/-- Assemble the four factor layers and their four padded center arrays. -/
def assemble (p₀ p₁ p₂ p₃ : QPoly4)
    (c₀ c₁ c₂ c₃ : Fin 4 → GaussianRat) : RawCertificate where
  factors := ![p₀, p₁, p₂, p₃]
  centers := ![c₀, c₁, c₂, c₃]

/-- Every positive tolerance admits a valid all-rational search certificate. -/
theorem exists_valid_certificate (p : QPoly4) (hp : (toPolynomial p).Monic)
    {ε : ℚ} (hε : 0 < ε) : ∃ raw, IsValid p ε raw := by
  obtain ⟨p₀, p₁, p₂, p₃, hm₀, hm₁, hm₂, hm₃,
      hs₀, hs₁, hs₂, hs₃, hprod, hdegree⟩ :=
    exists_four_bounded_monic_separable_factors p hp
  obtain ⟨c₀, ha₀, he₀, hd₀⟩ := exists_padded_autoValid_centers p₀ hs₀ hε
  obtain ⟨c₁, ha₁, he₁, hd₁⟩ := exists_padded_autoValid_centers p₁ hs₁ hε
  obtain ⟨c₂, ha₂, he₂, hd₂⟩ := exists_padded_autoValid_centers p₂ hs₂ hε
  obtain ⟨c₃, ha₃, he₃, hd₃⟩ := exists_padded_autoValid_centers p₃ hs₃ hε
  let raw := assemble p₀ p₁ p₂ p₃ c₀ c₁ c₂ c₃
  refine ⟨raw, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp only [raw, assemble, leadingCoeff_eq_toPolynomial] <;>
      assumption
  · apply productMatches_of_toPolynomial_eq
    rw [toPolynomial_factorProduct]
    simpa [raw, assemble] using hprod
  · simpa [factorDegreeSum, raw, assemble] using hdegree
  · intro i j hj
    fin_cases i
    · exact ha₀ j (by simpa [raw, assemble, Active] using hj)
    · exact ha₁ j (by simpa [raw, assemble, Active] using hj)
    · exact ha₂ j (by simpa [raw, assemble, Active] using hj)
    · exact ha₃ j (by simpa [raw, assemble, Active] using hj)
  · intro i j hj
    fin_cases i
    · simpa [raw, assemble, radius] using he₀ j
        (by simpa [raw, assemble, Active] using hj)
    · simpa [raw, assemble, radius] using he₁ j
        (by simpa [raw, assemble, Active] using hj)
    · simpa [raw, assemble, radius] using he₂ j
        (by simpa [raw, assemble, Active] using hj)
    · simpa [raw, assemble, radius] using he₃ j
        (by simpa [raw, assemble, Active] using hj)
  · intro i j j' hj hj' hjne
    fin_cases i
    · simpa [raw, assemble, radius] using hd₀ j j'
        (by simpa [raw, assemble, Active] using hj)
        (by simpa [raw, assemble, Active] using hj') hjne
    · simpa [raw, assemble, radius] using hd₁ j j'
        (by simpa [raw, assemble, Active] using hj)
        (by simpa [raw, assemble, Active] using hj') hjne
    · simpa [raw, assemble, radius] using hd₂ j j'
        (by simpa [raw, assemble, Active] using hj)
        (by simpa [raw, assemble, Active] using hj') hjne
    · simpa [raw, assemble, radius] using hd₃ j j'
        (by simpa [raw, assemble, Active] using hj)
        (by simpa [raw, assemble, Active] using hj') hjne

end GaussianPolynomialApproximationCertificateExistence

end LeanProofs.PolynomialFormulas
