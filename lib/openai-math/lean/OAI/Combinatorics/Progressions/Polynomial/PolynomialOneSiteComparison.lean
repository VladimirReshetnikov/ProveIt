import OAI.Combinatorics.Progressions.Lattices.AffineOneSiteNormalizedLaw

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

theorem exists_polynomial_oneSite_comparison (m e : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hI : (Fintype.card I : ℝ) ≤ P) (_hK : (Fintype.card K : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (root : K → ℤ) (_hroot : ∀ k, |(root k : ℝ)| ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hfreq : ∀ a j d, d.degree ≤ j.val+1 → ∀ t, |(frequency a j d t : ℝ)| ≤ Real.exp ((P+e)^e))
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
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ)
    (_hD : ∀ y, Integrable (fun x => D (coefficientFiberMap U root y x)) μ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η)
    (φ : (I → ℝ) → ℂ) (_hφ : ∀ v, ‖φ v‖ ≤ 1),
    let sample := fun z : Option K × I → ℤ =>
      affineSampleCoefficientTorus U p _hm (fun k j => (z (k,j) : ℝ))
    let fiber := fun z => coefficientFiberAverage U μ root D (coefficientEvaluationTorus U root (sample z))
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T V z,
      ‖(∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
          (φ (physicalAffineSite root z) * (D (sample z) : ℂ))) -
        (∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
          (φ (physicalAffineSite root z) * (fiber z : ℂ)))‖ ≤ 2*η+ε := by
  obtain ⟨A₀, _, hcomparison⟩ := exists_affine_oneSite_density_comparison m
  obtain ⟨A, hA, hthreshold⟩ := exists_polynomial_density_threshold e A₀
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hI hK U _ _ μ _ _ root hroot frequency hfreq c hcoeff
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR
    T hT V hV hwidth D hD η hη happrox φ hφ
  let difference : Fin 0 → K → ℤ := fun i => Fin.elim0 i
  have hsite (s : Finset (Fin 0)) (k : K) :
      |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ Real.exp P := by
    have hs : s = ∅ := Subsingleton.elim _ _
    simpa only [hs, affineSite, Finset.sum_empty, add_zero] using hroot k
  have hdom := polynomialDensityBudget_dominates e hP
  have hexp := Real.exp_le_exp.mpr hdom.1
  have hFourier := Real.exp_le_exp.mpr hdom.2.1
  have hlarge := Real.exp_le_exp.mpr (hthreshold P hP)
  obtain ⟨hZ, he⟩ := hcomparison (polynomialDensityBudget_nonneg e hP) (hI.trans hdom.1)
    (coefficientSampleDomain_card_le_budget e hP hI hK) U μ root difference
    (Real.exp_nonneg _) (Real.exp_nonneg _) hexp hFourier hsite frequency hfreq c
    (Real.exp_nonneg _) hFourier hcoeff p hp hm stride hs hS (hSP.trans hexp)
    hρ hε (hρP.trans hexp) (hεP.trans hexp) hstride H (fun k => hlarge.trans (hsize k))
    hrank (hlarge.trans hR) 0 (by simp) (fun _ => φ) (fun _ => hφ) T hT V hV hwidth
    D hD hη (fun x => by rw [norm_sub_rev]; exact happrox x)
  exact ⟨hZ, by simpa only [layeredSiteWeight_physical] using he⟩

end Erdos3.BooleanCubeKernel

end

end OAI
