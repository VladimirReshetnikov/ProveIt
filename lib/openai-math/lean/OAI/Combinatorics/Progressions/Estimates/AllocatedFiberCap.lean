/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Fourier.CoefficientEvaluationTorus
import OAI.Combinatorics.Progressions.Lattices.CenteredAffineCoefficient
import OAI.Combinatorics.Progressions.Probability.CanonicalConstantDensityBound
import OAI.Combinatorics.Progressions.Probability.CoefficientProductLaw
import OAI.Combinatorics.Progressions.Sampling.SelectedSamplerNormalization

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def coefficientFiberMap {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (y : CoefficientTorus (K := Empty) U) (x : CoefficientTorus (K := K) U) :
    CoefficientTorus (K := K) U :=
  constantCoefficientTorusMap U y +
    (x - constantCoefficientTorusMap U (coefficientEvaluationTorus U t x))

theorem coefficientFiberMap_evaluation {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (y : CoefficientTorus (K := Empty) U) (x : CoefficientTorus (K := K) U) :
    coefficientEvaluationTorus U t (coefficientFiberMap U t y x) = y := by
  simp only [coefficientFiberMap, map_add, map_sub, coefficientEvaluationTorus_constant,
    sub_self, add_zero]

theorem coefficientFiberMap_retraction {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (x : CoefficientTorus (K := K) U) :
    coefficientFiberMap U t (coefficientEvaluationTorus U t x) x = x := by
  dsimp only [coefficientFiberMap]
  abel

theorem coefficientFiberMap_nonconstant {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (y : CoefficientTorus (K := Empty) U) (x : CoefficientTorus (K := K) U)
    (s : CoefficientSlot K m) (hs : s.2.val ≠ 0) :
    coefficientCoordinateTorus U (coefficientFiberMap U t y x) s =
      coefficientCoordinateTorus U x s := by
  simp only [coefficientFiberMap, map_add, map_sub, Pi.add_apply, Pi.sub_apply,
    constantCoefficientTorusMap_nonconstant U _ s hs, sub_zero, zero_add]

theorem coefficientFiberMap_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (y : CoefficientTorus (K := Empty) U) : Continuous (coefficientFiberMap U t y) :=
  continuous_const.add (continuous_id.sub ((constantCoefficientTorusMap_continuous U).comp
    (coefficientEvaluationTorus_continuous U t)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coefficientConstantCenter :
    CoefficientTorus (K := K) U →+ CoefficientTorus (K := K) U :=
  (constantCoefficientTorusMap U).comp (coefficientEvaluationTorus U 0)

theorem coefficientConstantCenter_continuous :
    Continuous (coefficientConstantCenter (K := K) U) :=
  (constantCoefficientTorusMap_continuous U).comp (coefficientEvaluationTorus_continuous U 0)

omit [∀ j, Fintype (J j)] in
theorem coefficientConstantCenter_add_constant
    (x : CoefficientTorus (K := K) U) (y : CoefficientTorus (K := Empty) U) :
    coefficientConstantCenter U (x + constantCoefficientTorusMap U y) =
      coefficientConstantCenter U x + constantCoefficientTorusMap U y := by
  simp only [coefficientConstantCenter, AddMonoidHom.comp_apply, map_add,
    coefficientEvaluationTorus_constant]

omit [∀ j, Fintype (J j)] in
theorem coefficientConstantCenter_idempotent (x : CoefficientTorus (K := K) U) :
    coefficientConstantCenter U (coefficientConstantCenter U x) = coefficientConstantCenter U x := by
  simp only [coefficientConstantCenter, AddMonoidHom.comp_apply, coefficientEvaluationTorus_constant]

omit [∀ j, Fintype (J j)] in
theorem coefficientConstantCenter_nonconstant (x : CoefficientTorus (K := K) U)
    (s : CoefficientSlot K m) (hs : s.2.val ≠ 0) :
    coefficientCoordinateTorus U (coefficientConstantCenter U x) s = 0 :=
  constantCoefficientTorusMap_nonconstant U _ s hs

omit [∀ j, Fintype (J j)] in
theorem coefficientConstantCenter_integral_add_constant
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant]
    (D : CoefficientTorus (K := K) U → ℝ) (y : CoefficientTorus (K := Empty) U) :
    (∫ c, D (coefficientConstantCenter U c + constantCoefficientTorusMap U y) ∂μ) =
      ∫ c, D (coefficientConstantCenter U c) ∂μ := by
  simpa only [add_comm (constantCoefficientTorusMap U y), coefficientConstantCenter_add_constant] using
    integral_add_left_eq_self (μ := μ) (fun c => D (coefficientConstantCenter U c))
      (constantCoefficientTorusMap U y)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

noncomputable def coefficientFiberAverage {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (CoefficientTorus (K := K) U)) (t : K → ℤ)
    (F : CoefficientTorus (K := K) U → E) (y : CoefficientTorus (K := Empty) U) : E :=
  ∫ x, F (coefficientFiberMap U t y x) ∂μ

theorem coefficientFiberAverage_bound {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ] (t : K → ℤ)
    (F : CoefficientTorus (K := K) U → E) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B)
    (y : CoefficientTorus (K := Empty) U) : ‖coefficientFiberAverage U μ t F y‖ ≤ B := by
  have h := norm_integral_le_of_norm_le (integrable_const B (μ := μ))
    (ae_of_all μ (fun x => hB (coefficientFiberMap U t y x)))
  simpa only [coefficientFiberAverage, integral_const, probReal_univ, one_smul] using h

theorem coefficientFiberAverage_approx {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ] (t : K → ℤ)
    (F G : CoefficientTorus (K := K) U → E) {ε : ℝ} (hε : ∀ x, ‖F x - G x‖ ≤ ε)
    (y : CoefficientTorus (K := Empty) U)
    (hF : Integrable (fun x => F (coefficientFiberMap U t y x)) μ)
    (hG : Integrable (fun x => G (coefficientFiberMap U t y x)) μ) :
    ‖coefficientFiberAverage U μ t F y - coefficientFiberAverage U μ t G y‖ ≤ ε := by
  simp only [coefficientFiberAverage]
  rw [← integral_sub hF hG]
  exact coefficientFiberAverage_bound U μ t (fun x => F x - G x) hε y

theorem coefficientFiberAverage_nonneg {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) (t : K → ℤ)
    (F : CoefficientTorus (K := K) U → ℝ) (hF : ∀ x, 0 ≤ F x)
    (y : CoefficientTorus (K := Empty) U) : 0 ≤ coefficientFiberAverage U μ t F y :=
  integral_nonneg (fun x => hF (coefficientFiberMap U t y x))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def nonconstantCoefficientFactor {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (s : CoefficientSlot K m) (x : SubspaceArrayTorus Unit (U s.1)) : ℝ :=
  if s.2.val = 0 then 1 else f s x

theorem constantCoefficientCap_product {K : Type*} [Fintype K] {m : ℕ} (C : Fin m → ℝ) :
    (∏ s : CoefficientSlot K m, if s.2.val = 0 then C s.1 else 1) = ∏ j, C j := by
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.prod_eq_single (zeroCoefficientExponent K (j.val + 1))]
  · simp [zeroCoefficientExponent]
  · intro d _ hd
    have hd0 : d.val ≠ 0 := fun he => hd (Subtype.ext he)
    simp [hd0]
  · simp

theorem coefficientProductDensity_fiber_bound {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hf0 : ∀ s x, 0 ≤ f s x) (C : Fin m → ℝ)
    (hC : ∀ (s : CoefficientSlot K m), s.2.val = 0 → ∀ x, f s x ≤ C s.1)
    (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) (x : CoefficientTorus (K := K) U) :
    coefficientProductDensity U f (coefficientFiberMap U t y x) ≤
      (∏ j, C j) * coefficientProductDensity U (nonconstantCoefficientFactor U f) x := by
  calc
    _ ≤ ∏ s : CoefficientSlot K m,
        (if s.2.val = 0 then C s.1 else 1) *
          nonconstantCoefficientFactor U f s (coefficientCoordinateTorus U x s) := by
      apply Finset.prod_le_prod₀ (fun s _ => hf0 s _)
      intro s _
      by_cases hs : s.2.val = 0
      · simpa only [nonconstantCoefficientFactor, ite_eq_left hs, mul_one] using hC s hs
          (coefficientCoordinateTorus U (coefficientFiberMap U t y x) s)
      · simp only [nonconstantCoefficientFactor, ite_eq_right hs, one_mul,
          coefficientFiberMap_nonconstant U t y x s hs, le_refl]
    _ = _ := by rw [Finset.prod_mul_distrib, constantCoefficientCap_product]; rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientFiberMap_translate (t : K → ℤ) (y : CoefficientTorus (K := Empty) U)
    (c x : CoefficientTorus (K := K) U) :
    c + coefficientFiberMap U t y x =
      coefficientFiberMap U t (y + coefficientEvaluationTorus U t c) (c+x) := by
  simp only [coefficientFiberMap, map_add]
  abel

theorem coefficientFiberAverage_translate
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : K → ℤ) (F : CoefficientTorus (K := K) U → E)
    (c : CoefficientTorus (K := K) U) (y : CoefficientTorus (K := Empty) U) :
    coefficientFiberAverage U μ t (fun x => F (c+x)) y =
      coefficientFiberAverage U μ t F (y + coefficientEvaluationTorus U t c) := by
  unfold coefficientFiberAverage
  simp_rw [coefficientFiberMap_translate]
  exact integral_add_left_eq_self (μ := μ)
    (fun x => F (coefficientFiberMap U t (y + coefficientEvaluationTorus U t c) x)) c

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} [Fintype K] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem coefficientMixedFiber_joint_measurable
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Measurable (fun p : CoefficientTorus (K := K) U × CoefficientTorus (K := K) U =>
      D (coefficientConstantCenter U p.1 + coefficientFiberMap U t y p.2)) :=
  hD.comp (((coefficientConstantCenter_continuous U).measurable.comp measurable_fst).add
    ((coefficientFiberMap_continuous U t y).measurable.comp measurable_snd))

theorem coefficientMixedFiber_joint_integrable
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    {M : ℝ} (hbound : ∀ x, ‖D x‖ ≤ M) (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun p : CoefficientTorus (K := K) U × CoefficientTorus (K := K) U =>
      D (coefficientConstantCenter U p.1 + coefficientFiberMap U t y p.2)) (μ.prod μ) :=
  Integrable.of_bound (coefficientMixedFiber_joint_measurable U D hD t y).aestronglyMeasurable
    M (ae_of_all _ (fun _ => hbound _))

theorem coefficientMixedFiber_integrable
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    {M : ℝ} (hbound : ∀ x, ‖D x‖ ≤ M) (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun c => coefficientFiberAverage U μ t
      (fun x => D (coefficientConstantCenter U c+x)) y) μ :=
  (coefficientMixedFiber_joint_integrable U μ D hD hbound t y).integral_prod_left

theorem coefficientMixedFiber_average
    (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Measurable D)
    {M : ℝ} (hbound : ∀ x, ‖D x‖ ≤ M) (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    (∫ c, coefficientFiberAverage U μ t (fun x => D (coefficientConstantCenter U c+x)) y ∂μ) =
      ∫ x, D x ∂μ := by
  have hi := coefficientMixedFiber_joint_integrable U μ D hD hbound t y
  have hi' : Integrable (fun p : CoefficientTorus (K := K) U × CoefficientTorus (K := K) U =>
      D (coefficientConstantCenter U p.1+p.2)) (μ.prod μ) :=
    Integrable.of_bound (hD.comp (((coefficientConstantCenter_continuous U).measurable.comp
      measurable_fst).add measurable_snd)).aestronglyMeasurable M (ae_of_all _ (fun _ => hbound _))
  have hshift (x : CoefficientTorus (K := K) U) :
      (∫ c, D (coefficientConstantCenter U c + coefficientFiberMap U t y x) ∂μ) =
        ∫ c, D (coefficientConstantCenter U c+x) ∂μ := by
    calc
      _ = ∫ c, D ((coefficientConstantCenter U c + constantCoefficientTorusMap U
          (y-coefficientEvaluationTorus U t x))+x) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ (fun c => by
          apply congrArg D
          simp only [coefficientFiberMap, map_sub]
          abel)
      _ = _ := coefficientConstantCenter_integral_add_constant U μ (fun z => D (z+x)) _
  change (∫ c, ∫ x, D (coefficientConstantCenter U c + coefficientFiberMap U t y x) ∂μ ∂μ) = _
  calc
    _ = ∫ x, ∫ c, D (coefficientConstantCenter U c + coefficientFiberMap U t y x) ∂μ ∂μ :=
      integral_integral_swap hi
    _ = ∫ x, ∫ c, D (coefficientConstantCenter U c+x) ∂μ ∂μ :=
      integral_congr_ae (ae_of_all μ hshift)
    _ = ∫ c, ∫ x, D (coefficientConstantCenter U c+x) ∂μ ∂μ :=
      (integral_integral_swap hi').symm
    _ = _ := by simp only [integral_add_left_eq_self, integral_const, probReal_univ, one_smul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem nonconstantCoefficientDensity_probability {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
    [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)]
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hfi : ∀ s, Integrable (f s) (ν s)) (hf0 : ∀ s x, 0 ≤ f s x)
    (hmass : ∀ s, (∫ x, f s x ∂ν s) = 1) :
    Integrable (coefficientProductDensity U (nonconstantCoefficientFactor U f)) μ ∧
      (∀ x, 0 ≤ coefficientProductDensity U (nonconstantCoefficientFactor U f) x) ∧
      (∫ x, coefficientProductDensity U (nonconstantCoefficientFactor U f) x ∂μ) = 1 := by
  apply coefficientProductDensity_probability U μ ν
  · intro s
    change Integrable (fun x => if s.2.val = 0 then 1 else f s x) (ν s)
    by_cases hs : s.2.val = 0
    · simpa only [ite_eq_left hs] using
        (integrable_const (1 : ℝ) (μ := ν s))
    · simpa only [ite_eq_right hs] using hfi s
  · intro s x
    by_cases hs : s.2.val = 0
    · simp only [nonconstantCoefficientFactor, ite_eq_left hs, zero_le_one]
    · simpa only [nonconstantCoefficientFactor, ite_eq_right hs] using hf0 s x
  · intro s
    by_cases hs : s.2.val = 0
    · simp only [nonconstantCoefficientFactor, ite_eq_left hs, integral_const,
        probReal_univ, one_smul]
    · simpa only [nonconstantCoefficientFactor, ite_eq_right hs] using hmass s

theorem coefficientProductDensity_fiberAverage_cap {K : Type*} [Fintype K] {m : ℕ}
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
    (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => coefficientProductDensity U f (coefficientFiberMap U t y x)) μ ∧
      coefficientFiberAverage U μ t (coefficientProductDensity U f) y ∈ Set.Icc (0 : ℝ) (∏ j, C j) := by
  have hR := nonconstantCoefficientDensity_probability U μ ν f hfi hf0 hmass
  have hD : Measurable (coefficientProductDensity U f) :=
    Finset.measurable_prod _ (fun s _ => (hf s).comp
      ((measurable_pi_apply s).comp (coefficientCoordinateTorus_continuous U).measurable))
  have hb := coefficientProductDensity_fiber_bound U f hf0 C hC t y
  have hi : Integrable (fun x => coefficientProductDensity U f (coefficientFiberMap U t y x)) μ :=
    (hR.1.const_mul (∏ j, C j)).mono'
      (hD.comp (coefficientFiberMap_continuous U t y).measurable).aestronglyMeasurable
      (ae_of_all μ (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (coefficientProductDensity_nonneg U f hf0 _)]
        exact hb x))
  refine ⟨hi, coefficientFiberAverage_nonneg U μ t _ (coefficientProductDensity_nonneg U f hf0) y, ?_⟩
  calc
    _ ≤ ∫ x, (∏ j, C j) * coefficientProductDensity U (nonconstantCoefficientFactor U f) x ∂μ :=
      integral_mono hi (hR.1.const_mul _) hb
    _ = ∏ j, C j := by rw [integral_const_mul, hR.2.2, mul_one]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

noncomputable def canonicalCoefficientFactor (s : CoefficientSlot K m)
    (y : SubspaceArrayTorus Unit (U s.1)) : ℝ :=
  canonicalMixedDensity (euclideanSubspace (U s.1)) (b s.1) (hb s.1) (o s.1)
    (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => p s.1 i s.2)
    ((euclideanSubspaceTorusEquiv (U s.1)).symm y)

theorem canonicalCoefficientDensity_product :
    canonicalCoefficientDensity U b hb o c w p =
      coefficientProductDensity U (canonicalCoefficientFactor U b hb o c w p) := by
  funext x
  unfold canonicalCoefficientDensity canonicalArrayDensity coefficientProductDensity
  rw [Fintype.prod_sigma]
  rfl

variable [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
variable [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]

omit [Fintype K] in
theorem canonicalCoefficientFactor_measurable (s : CoefficientSlot K m) :
    Measurable (canonicalCoefficientFactor U b hb o c w p s) :=
  (canonicalMixedDensity_measurable _ (b s.1) (hb s.1) (o s.1) _ _ _).comp
    (euclideanSubspaceTorusMeasurableEquiv (U s.1)).symm.measurable

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

include ν in
theorem canonicalCoefficientDensity_fiber_cap (hw : ∀ j i d, 0 < w j i d)
    (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
      (fun i => p j i d) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))
    (C : Fin m → ℝ)
    (hC : ∀ (s : CoefficientSlot K m), s.2.val = 0 → ∀ y,
      canonicalCoefficientFactor U b hb o c w p s y ≤ C s.1)
    (t : K → ℤ) (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => canonicalCoefficientDensity U b hb o c w p (coefficientFiberMap U t y x)) μ ∧
      coefficientFiberAverage U μ t (canonicalCoefficientDensity U b hb o c w p) y ∈
        Set.Icc (0 : ℝ) (∏ j, C j) := by
  let ξ := fun s : CoefficientSlot K m => euclideanSubspaceTorusMeasure (U s.1) (ν s.1)
  let : ∀ s, IsProbabilityMeasure (ξ s) :=
    fun s => euclideanSubspaceTorusMeasure_probability (U s.1) (ν s.1)
  let : ∀ s, (ξ s).IsAddLeftInvariant :=
    fun s => euclideanSubspaceTorusMeasure_invariant (U s.1) (ν s.1)
  have hmass (s : CoefficientSlot K m) := canonicalMixedDensity_mass _ (b s.1) (hb s.1) (o s.1)
    (ν s.1) (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => hw s.1 i s.2)
    (fun i => p s.1 i s.2) (hs s.1 s.2)
  have hfactor (s : CoefficientSlot K m) := euclideanSubspaceTorusMeasure_mass (U s.1) (ν s.1)
    _ (hmass s).1 (hmass s).2
  rw [canonicalCoefficientDensity_product]
  exact coefficientProductDensity_fiberAverage_cap U μ ξ (canonicalCoefficientFactor U b hb o c w p)
    (canonicalCoefficientFactor_measurable U b hb o c w p) (fun s => (hfactor s).1)
    (fun s x => canonicalMixedDensity_nonneg _ (b s.1) (hb s.1) (o s.1) _ _
      (fun i => hw s.1 i s.2) _ _) (fun s => (hfactor s).2) C hC t y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
variable [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))

omit [∀ j, Fintype (J j)] in
theorem exists_subtractive_constant_center (x : CoefficientTorus (K := K) U) :
    ∃ c : ∀ j, U j, coefficientConstantCenter U x =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray (K := K) U (fun s => c s.1))) := by
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U)
    (-(coefficientEvaluationTorus U 0 x))
  let c := fun j => v ⟨j, zeroCoefficientExponent Empty (j.val + 1)⟩
  have hc : (fun s : CoefficientSlot Empty m => c s.1) = v := by
    funext s
    rcases s with ⟨j,d⟩
    rw [emptyCoefficientExponent_eq (j.val + 1) d]
  refine ⟨c, ?_⟩
  rw [← constantCoefficientTorusMap_mk, hc, hv, map_neg, neg_neg]
  rfl

omit [∀ j, Fintype (J j)] in
theorem centeredAffineCoefficientTorus_eq_subtractive {V : Type*}
    (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (c : ∀ j, U j) (frame : Option K → V → ℝ) :
    centeredAffineCoefficientTorus U p hm c frame =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))) +
      affineSampleCoefficientTorus U p hm frame := by
  rw [centeredAffineCoefficientTorus, centeredAffineCoefficientArray, map_sub]
  exact sub_eq_neg_add _ _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (V : Fin m → ℝ) (hV : ∀ j, 0 ≤ V j)
variable (hv : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hV hv in
theorem allocatedCoefficientFactor_constant_cap
    (s : CoefficientSlot (LayerSamplerVariables G I n B) m) (hs : s.2.val = 0)
    (y : SubspaceArrayTorus Unit (U s.1)) :
    canonicalCoefficientFactor U b hb o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerPMFs B U b hR hσ S) s y ≤
      earlyConstantDensityCap (Fintype.card (I s.1)) (n s.1) (R s.1) (V s.1) := by
  rcases s with ⟨j, d⟩
  have hd : d = constantCoefficientSlot _ _ := Subtype.ext hs
  subst d
  simpa only [canonicalCoefficientFactor, allocatedLayerCenters_constant,
    allocatedLayerWidths_constant, allocatedLayerIntegerPMFs_constant] using
    canonicalMixedDensity_constant_cap (euclideanSubspace (U j)) (b j) (hb j) (o j)
      (hR j) (hV j) (hv j) ((euclideanSubspaceTorusEquiv (U j)).symm y)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

include hV hv ν hσ1 Cinv hCinv hchart hsmall

theorem allocatedCoefficientDensity_fiber_cap (t : LayerSamplerVariables G I n B → ℤ)
    (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => allocatedCoefficientDensity B U b hb o hR hσ S (coefficientFiberMap U t y x)) μ ∧
      coefficientFiberAverage U μ t (allocatedCoefficientDensity B U b hb o hR hσ S) y ∈
        Set.Icc (0 : ℝ) (∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) := by
  let : ∀ j, BorelSpace (SubspaceArrayTorus Unit (U j)) := fun _ => QuotientAddGroup.borelSpace
  exact canonicalCoefficientDensity_fiber_cap U b hb o _ _ _ μ ν
    (allocatedLayerWidths_pos B U b hR hσ S)
    (allocatedLayerColumns_chart B U b hR hσ S o hσ1 Cinv hCinv hchart hsmall)
    (fun j => earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j))
    (allocatedCoefficientFactor_constant_cap B U b hb o hR hσ S V hV hv) t y

theorem selectedCoefficientDensity_fiber_cap (L₀ : ℕ) (t : LayerSamplerVariables G I n B → ℤ)
    (y : CoefficientTorus (K := Empty) U) :
    Integrable (fun x => selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀
        (coefficientFiberMap U t y x)) μ ∧
      coefficientFiberAverage U μ t (selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀) y ∈
        Set.Icc (0 : ℝ) (∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) :=
  allocatedCoefficientDensity_fiber_cap B U b hb o hR hσ
    (selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀) V hV hv μ ν hσ1 Cinv hCinv hchart hsmall t y

end Erdos3.VectorPolynomial

end

end OAI
