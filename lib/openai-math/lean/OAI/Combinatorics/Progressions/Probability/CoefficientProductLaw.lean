/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Pass sigma-finiteness explicitly to the product-integral theorem on Lean 4.32.
Mathematical statements are unchanged. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.CoefficientProductHaar

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

noncomputable def coefficientProductDensity {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (x : CoefficientTorus (K := K) U) : ℝ := ∏ s, f s (coefficientCoordinateTorus U x s)

theorem coefficientProductDensity_nonneg {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hf : ∀ s x, 0 ≤ f s x) (x : CoefficientTorus (K := K) U) :
    0 ≤ coefficientProductDensity U f x := Finset.prod_nonneg (fun s _ => hf s _)

theorem coefficientProductDensity_bound {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (B : CoefficientSlot K m → ℝ) (hf : ∀ s x, 0 ≤ f s x) (hB : ∀ s x, f s x ≤ B s)
    (x : CoefficientTorus (K := K) U) : coefficientProductDensity U f x ≤ ∏ s, B s :=
  Finset.prod_le_prod₀ (fun s _ => hf s _) (fun s _ => hB s _)

theorem coefficientProductDensity_ne_zero_factors {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    {x : CoefficientTorus (K := K) U} (hx : coefficientProductDensity U f x ≠ 0)
    (s : CoefficientSlot K m) : f s (coefficientCoordinateTorus U x s) ≠ 0 :=
  (Finset.prod_ne_zero_iff.mp hx) s (Finset.mem_univ s)

theorem coefficientProductDensity_probability {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ s : CoefficientSlot K m, MeasurableSpace (SubspaceArrayTorus Unit (U s.1))]
    [∀ s : CoefficientSlot K m, BorelSpace (SubspaceArrayTorus Unit (U s.1))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)]
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hf : ∀ s, Integrable (f s) (ν s)) (hf0 : ∀ s x, 0 ≤ f s x)
    (hmass : ∀ s, (∫ x, f s x ∂ν s) = 1) :
    Integrable (coefficientProductDensity U f) μ ∧
      (∀ x, 0 ≤ coefficientProductDensity U f x) ∧
      (∫ x, coefficientProductDensity U f x ∂μ) = 1 := by
  let g : CoefficientCoordinateTori (K := K) U → ℝ := fun y => ∏ s, f s (y s)
  have hg : Integrable g (Measure.pi ν) := Integrable.fintype_prod_dep hf
  have hp := coefficientCoordinateTorus_measurePreserving U μ ν
  refine ⟨hp.integrable_comp_of_integrable hg, coefficientProductDensity_nonneg U f hf0, ?_⟩
  have hg' : AEStronglyMeasurable g (Measure.map (coefficientCoordinateTorus U) μ) := by
    simpa only [hp.map_eq] using hg.aestronglyMeasurable
  calc
    (∫ x, coefficientProductDensity U f x ∂μ) = ∫ y, g y ∂Measure.pi ν := by
      simpa only [hp.map_eq, g, coefficientProductDensity] using
        (integral_map hp.measurable.aemeasurable hg').symm
    _ = ∏ s, ∫ x, f s x ∂ν s :=
      @integral_fintype_prod_eq_prod ℝ (CoefficientSlot K m) _ _ _ f _ ν
        (fun s => IsFiniteMeasure.toSigmaFinite (ν s))
    _ = 1 := by simp only [hmass, Finset.prod_const_one]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

theorem coefficientProductDensity_coordinate_law {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ s : CoefficientSlot K m, MeasurableSpace (SubspaceArrayTorus Unit (U s.1))]
    [∀ s : CoefficientSlot K m, BorelSpace (SubspaceArrayTorus Unit (U s.1))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)]
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hf : ∀ s, Measurable (f s)) (hfi : ∀ s, Integrable (f s) (ν s))
    (hf0 : ∀ s x, 0 ≤ f s x) :
    (realDensityMeasure μ (coefficientProductDensity U f)).map (coefficientCoordinateTorus U) =
      Measure.pi (fun s => realDensityMeasure (ν s) (f s)) := by
  let _ : ∀ s, SigmaFinite (ν s) := fun s => inferInstance
  let D : CoefficientCoordinateTori (K := K) U → ℝ := fun x => ∏ s, f s (x s)
  have hD : Measurable D := Finset.measurable_prod _ (fun s _ => (hf s).comp (measurable_pi_apply s))
  have hDi : Integrable D (Measure.pi ν) := Integrable.fintype_prod_dep hfi
  have hD0 (x) : 0 ≤ D x := Finset.prod_nonneg (fun s _ => hf0 s _)
  have hp := coefficientCoordinateTorus_measurePreserving U μ ν
  have ht := measurePreserving_realDensity_map μ (Measure.pi ν) (coefficientCoordinateTorus U)
    hp D hD hDi hD0
  have he : Measure.pi (fun s => realDensityMeasure (ν s) (f s)) = realDensityMeasure (Measure.pi ν) D :=
    realDensityMeasure_pi ν f hfi hf0
  exact ht.trans he.symm

end Erdos3.VectorPolynomial

end

end OAI
