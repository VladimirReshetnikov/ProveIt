import OAI.Combinatorics.Progressions.Fourier.OneSiteFourierAverage

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

theorem affineCubeFourierProjection_approx {I K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) {η : ℝ}
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (b : Option K → I → ℝ)
    (hD : Integrable (fun x => D (coefficientFiberMap U t
      (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm b)) x)) μ) :
    ‖affineCubeFourierProjection U t difference frequency p c b -
      ((coefficientFiberAverage U μ t D
        (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm b)) : ℝ) : ℂ)‖ ≤ η := by
  rw [affineCubeFourierProjection_eq_fiberAverage U t difference frequency c μ p hp hm b]
  have he := coefficientFiberAverage_approx U μ t (coefficientTorusFourierSum U frequency c)
    (fun x => (D x : ℂ)) happrox _
    (coefficientTorusFourierSum_fiber_integrable U t frequency c μ _) hD.ofReal
  simpa only [coefficientFiberAverage, integral_complex_ofReal] using he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

theorem oneSiteDensity_projection_error {X I K F : Type*} [Fintype X] [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) {η ε B : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (prob : FiniteProbabilityWeights X) (b : X → Option K → I → ℝ) (w : X → ℂ)
    (hD : ∀ x, prob.weight x ≠ 0 → Integrable (fun z => D (coefficientFiberMap U t
      (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm (b x))) z)) μ)
    (hw : prob.mean (fun x => ‖w x‖) ≤ B)
    (hprojection : ‖prob.complexMean (fun x => w x * affineCubeFourierSum frequency p c (b x)) -
      prob.complexMean (fun x => w x * affineCubeFourierProjection U t difference frequency p c (b x))‖ ≤ ε) :
    ‖prob.complexMean (fun x => w x * (D (affineSampleCoefficientTorus U p hm (b x)) : ℂ)) -
      prob.complexMean (fun x => w x * ((coefficientFiberAverage U μ t D
        (coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm (b x))) : ℝ) : ℂ))‖ ≤
      2 * B * η + ε := by
  apply prob.weighted_projection_comparison w _
    (fun x => affineCubeFourierSum frequency p c (b x))
    (fun x => affineCubeFourierProjection U t difference frequency p c (b x)) _ hη hw
  · intro x _
    rw [norm_sub_rev]
    simpa only [affineCubeFourierSum, coefficientTorusFourierSum,
      coefficientTorusCharacter_sample U _ p hp hm] using happrox (affineSampleCoefficientTorus U p hm (b x))
  · intro x hx
    exact affineCubeFourierProjection_approx U t difference frequency c μ D happrox p hp hm (b x) (hD x hx)
  · exact hprojection

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

theorem affineCubeFourierProjection_product_cap {I K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
    [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)]
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hf : ∀ s, Measurable (f s)) (hfi : ∀ s, Integrable (f s) (ν s))
    (hf0 : ∀ s x, 0 ≤ f s x) (hmass : ∀ s, (∫ x, f s x ∂ν s) = 1)
    (C : Fin m → ℝ)
    (hC : ∀ (s : CoefficientSlot K m), s.2.val = 0 → ∀ x, f s x ≤ C s.1)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ) {η : ℝ}
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x -
      (coefficientProductDensity U f x : ℂ)‖ ≤ η)
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (b : Option K → I → ℝ) :
    ‖affineCubeFourierProjection U t difference frequency p c b‖ ≤ (∏ j, C j) + η := by
  let y := coefficientEvaluationTorus U t (affineSampleCoefficientTorus U p hm b)
  let D := coefficientProductDensity U f
  let A := affineCubeFourierProjection U t difference frequency p c b
  let d := coefficientFiberAverage U μ t D y
  have hd := coefficientProductDensity_fiberAverage_cap U μ ν f hf hfi hf0 hmass C hC t y
  have he : ‖A - (d : ℂ)‖ ≤ η :=
    affineCubeFourierProjection_approx U t difference frequency c μ D happrox p hp hm b hd.1
  have hdn : ‖(d : ℂ)‖ ≤ ∏ j, C j := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd.2.1]
    exact hd.2.2
  change ‖A‖ ≤ _
  calc
    ‖A‖ = ‖(A - (d : ℂ)) + (d : ℂ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖A - (d : ℂ)‖ + ‖(d : ℂ)‖ := norm_add_le _ _
    _ ≤ η + ∏ j, C j := add_le_add he hdn
    _ = _ := add_comm _ _

end Erdos3.BooleanCubeKernel

end

end OAI
