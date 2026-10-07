import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import OAI.Combinatorics.Progressions.Fourier.AnchoredCoefficientFourierNormalization
import OAI.Combinatorics.Progressions.Fourier.SiteFourierHaarMean
import OAI.Combinatorics.Progressions.Probability.ProbabilityIntegralApproximation

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem selectedResidueSmoothPMF_weighted_coefficient_density
    {I K L F : Type*} [Fintype I] [Fintype K] [Fintype L] [Fintype F]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern L I modulus))
    (V : L × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (sample : (L × I → ℤ) → CoefficientTorus (K := K) U)
    (w : (L × I → ℤ) → ℂ)
    (hw : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖w x‖ ≤ 1)
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Integrable D μ)
    (hDmass : (∫ x, D x ∂μ) = 1)
    {η ε : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η)
    (hfourier : ‖(∑' z, ((selectedResidueSmoothPMF modulus G V hV hZ z).toReal : ℂ) *
        (w z * coefficientTorusFourierSum U frequency c (sample z))) -
      (∑' z, ((selectedResidueSmoothPMF modulus G V hV hZ z).toReal : ℂ) * w z) *
        (∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0)‖ ≤ ε) :
    ‖(∑' z, ((selectedResidueSmoothPMF modulus G V hV hZ z).toReal : ℂ) *
        (w z * (D (sample z) : ℂ))) -
      ∑' z, ((selectedResidueSmoothPMF modulus G V hV hZ z).toReal : ℂ) * w z‖ ≤
        2 * η + ε := by
  classical
  have hmass := probability_integral_approximation μ
    (coefficientTorusFourierSum U frequency c) (fun x => (D x : ℂ))
    (coefficientTorusFourierSum_integrable U frequency c μ) hD.ofReal
    (fun x => by simpa only [norm_sub_rev] using happrox x)
  rw [coefficientTorusFourierSum_integral, integral_complex_ofReal, hDmass,
    Complex.ofReal_one] at hmass
  have h := selectedResidueSmoothPMF_projection_approximation modulus G V hV hZ
    w (fun z => (D (sample z) : ℂ))
    (fun z => coefficientTorusFourierSum U frequency c (sample z))
    (fun _ => ∑ a, if affineCoefficientModeTrivial U (frequency a) then c a else 0)
    (fun _ => 1) hη hw (fun z _ => happrox (sample z)) (fun _ _ => hmass)
    (by simpa only [← mul_assoc, tsum_mul_right] using hfourier)
  simpa only [mul_one] using h

end Erdos3.VectorPolynomial

end

end OAI
