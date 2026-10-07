import OAI.Combinatorics.Progressions.Geometry.DetectedTranslationLogCoordinates

namespace OAI

section

namespace Erdos3

theorem scaleMvPolynomialAxes_mass_le_of_totalDegree {U : Type*} [Fintype U]
    (T : U → ℝ) (hT : ∀ i, 0 < T i) (P : MvPolynomial U ℝ)
    {d : ℕ} (hd : P.totalDegree ≤ d) {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ α, |P.coeff α| ≤ A / monomialScale T α) :
    realPolynomialMass (scaleMvPolynomialAxes T P) ≤
      ((Fintype.card U : ℝ) + 1) ^ d * A := by
  apply (scaleMvPolynomialAxes_mass_le T hT P hcoeff).trans
  apply mul_le_mul_of_nonneg_right _ hA
  exact_mod_cast mvPolynomial_support_card_le_totalDegree P hd

namespace PolynomialTranslationLie

open Module VectorPolynomial RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

theorem detectedTranslationLogCoordinate_totalDegree
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (k : WeightedBasisIndex w d) :
    (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k).totalDegree ≤ d :=
  (degreeLE_one_iff_basis_totalDegree ((weightedBasis w d hw).baseChange ℝ) d
    (detectedTranslationSymbolLift w d hw hwd M hM D E).log).mp
      (detectedTranslationSymbolLift w d hw hwd M hM D E).degreeLE k

theorem detectedTranslationLogCoordinate_normalized_mass [Fintype U] [Fintype ι]
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j,
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j =
        Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (T : U → ℝ) (hT : ∀ i, 0 < T i) {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (k : WeightedBasisIndex w d)
    (hproj : ∀ i, |(detectedTranslationLogProjectionMatrix w d hw b ω k i : ℝ)| ≤ H)
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hE : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.SymbolSlowBound
      b ω hN (fun _ : U => 1) T A E) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (detectedTranslationLogCoordinatePolynomial w d hw hwd M hM D E k)) ≤
        ((Fintype.card U : ℝ) + 1) ^ d * ((Fintype.card ι : ℝ) * H * A) := by
  apply scaleMvPolynomialAxes_mass_le_of_totalDegree T hT _
    (detectedTranslationLogCoordinate_totalDegree w d hw hwd M hM D E k)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hH) hA)
  exact detectedTranslationLogCoordinate_slow_coefficients w d hw hwd M hM D b ω hN
    T hT hA hH k hproj E hE

end PolynomialTranslationLie
end Erdos3

end

end OAI
