import OAI.Combinatorics.Progressions.Lattices.AffineCoefficientCoverTilt

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_polynomial_coefficient_density_mass (m e : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hI : (Fintype.card I : ℝ) ≤ P)
    (_hK : (Fintype.card K : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hfreq : ∀ a j d, d.degree ≤ j.val+1 → ∀ t,
      |(frequency a j d t : ℝ)| ≤ Real.exp ((P+e)^e))
    (c : F → ℂ) (_hcoeff : (∑ a, ‖c a‖) ≤ Real.exp ((P+e)^e))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val+1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P)
    (_hρ : 0 < ρ) (_hε : 0 < ε) (_hρP : 1/ρ ≤ Real.exp P) (_hεP : 1/ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ H k)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) H R (U j) (p j))
    (_hR : Real.exp ((P+A)^A) ≤ R)
    (T : Finset (ColumnResiduePattern (Option K) I stride)) (_hT : T.Nonempty)
    (V : Option K × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ) (_hD : Integrable D μ)
    (_hDmass : (∫ x, D x ∂μ) = 1) {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride T V x,
      |selectedResidueDensityMass stride T V
        (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k,j) : ℝ)))) - 1| ≤
        2*η+ε := by
  obtain ⟨A₀, _, hmass⟩ := exists_affine_coefficient_density_mass m
  obtain ⟨A, hA, hthreshold⟩ := exists_polynomial_density_threshold e A₀
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hI hK U _ _ μ _ _ frequency hfreq c hcoeff
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR
    T hT V hV hwidth D hD hDmass η hη happrox
  have hdom := polynomialDensityBudget_dominates e hP
  have hexp := Real.exp_le_exp.mpr hdom.1
  have hFourier := Real.exp_le_exp.mpr hdom.2.1
  have hlarge := Real.exp_le_exp.mpr (hthreshold P hP)
  exact hmass (polynomialDensityBudget_nonneg e hP) (hI.trans hdom.1)
    (coefficientSampleDomain_card_le_budget e hP hI hK) U μ
    (Real.exp_nonneg _) hFourier frequency hfreq c (Real.exp_nonneg _) hFourier hcoeff
    p hp hm stride hs hS (hSP.trans hexp) hρ hε (hρP.trans hexp) (hεP.trans hexp) hstride
    H (fun k => hlarge.trans (hsize k)) hrank (hlarge.trans hR) T hT V hV hwidth
    D hD hDmass hη happrox

end Erdos3.VectorPolynomial

end

end OAI
