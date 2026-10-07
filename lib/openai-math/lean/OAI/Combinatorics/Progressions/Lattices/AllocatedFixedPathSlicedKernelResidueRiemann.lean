import Mathlib.Analysis.Calculus.MeanValue
import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleFullSliceLipschitz
import OAI.Combinatorics.Progressions.Lattices.AffineKernelResidueRetained
import OAI.Combinatorics.Progressions.Linear.ContainedKernelPhysicalDisplacement
import OAI.Combinatorics.Progressions.Sampling.AllocatedKernelForecastSourceDecoupling

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

include hR hσ in
theorem allocatedOriginalSampleFullSlice_residue_riemann (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (step H M : Input → ℕ) (c : Input → ℤ)
    (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : Input → Option Empty → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((M j : ℝ) / H j) < 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / S.value ≤ ε)
    (φ : (Output → ℝ) → ℝ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (a : Active) (p : B a.val × Fin (degree a.val)) => (c ⟨a, p⟩ : ℝ) / S.value
    let width := fun (a : Active) (p : B a.val × Fin (degree a.val)) =>
      (step ⟨a, p⟩ : ℝ) * ((H ⟨a, p⟩ : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights Empty (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j)
        (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j))).mean
        (fun z => φ (allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => ((c j : ℝ) + (step j : ℝ) * (z j none : ℝ)) / S.value))) -
      ∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
        ∂unitBoxMeasure Input| ≤
      (2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε := by
  classical
  intro lower width K
  let F := allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1) sample
  let project := fun x : Input → Option Empty → ℝ => fun j => x j none
  have hproj : LipschitzWith 1 project := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro j
    exact (dist_le_pi_dist (x j) (y j) none).trans (dist_le_pi_dist x y j)
  have hball : Set.MapsTo project (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    exact (norm_le_pi_norm (x j) none).trans ((norm_le_pi_norm x j).trans hx)
  have hF := allocatedOriginalSampleFullSliceMap_supported_lipschitzOn B U basis hR hσ S x u sample hs
    (fun _ _ => 0) (fun _ _ => 1) (by intro _ _; norm_num) ht hσbound
  have htest : LipschitzOnWith K (fun x => φ (F (project x))) (Metric.closedBall 0 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    calc
      _ ≤ Kφ * dist (F (project x)) (F (project y)) := hφ.dist_le_mul _ _
      _ ≤ Kφ * ((allocatedOriginalSampleFullSliceLip B U basis S t : ℝ) *
          dist (project x) (project y)) :=
        mul_le_mul_of_nonneg_left (hF.dist_le_mul _ (hball hx) _ (hball hy)) Kφ.coe_nonneg
      _ ≤ Kφ * ((allocatedOriginalSampleFullSliceLip B U basis S t : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by simpa using hproj.dist_le_mul x y)
            (allocatedOriginalSampleFullSliceLip B U basis S t).coe_nonneg) Kφ.coe_nonneg
      _ = K * dist x y := by simp only [K, NNReal.coe_mul, mul_assoc]
  have he := progressionTuple_residue_riemann_on_box (fun _ : Input => S.value)
    step H M c (fun _ => S.positive) hstep hH hδ hsubset hdense modulus residue hm hmM
    (fun j => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize j)
    (fun j => by simpa only [Measure.real, scalarCubeDomain_empty_volume, ENNReal.toReal_one]
      using hsmall j) hε hmesh (fun x => φ (F (project x))) htest zero_le_one
    (fun x _ => hφone _)
  have hid (z : Input → Option Empty → ℝ) :
      F (project (affineCubeTuple (fun j => (c j : ℝ) / S.value)
        (fun j => (step j : ℝ) * ((H j : ℝ) - 1) / S.value) z)) =
      allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample (project z) := by
    exact allocatedOriginalSampleFullSliceMap_affine B U basis S x u sample lower width (project z)
  simp_rw [hid] at he
  have hmeas : Measurable (fun y =>
      φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)) :=
    hφ.continuous.measurable.comp
      (allocatedOriginalSampleFullSliceMap_measurable B U basis S x u lower width sample)
  rw [scalarCubeProductMeasure_empty_integral Input _ hmeas] at he
  simpa only [F, project, ite_true, Measure.real, scalarCubeDomain_empty_volume,
    ENNReal.toReal_one, mul_one, div_one] using he

include hR hσ in
theorem allocatedOriginalSampleFullSlice_full_residue_real_riemann
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (hS : 2 ≤ S.value) (q : ℕ) (hq : 0 < q)
    (residue : Input → Option Empty → ZMod q)
    (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (φ : (Output → ℝ) → ℝ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    |(principalResidueWeights (fun a : Active => B a.val) (fun a : Active => degree a.val)
        (fun _ => S.value) (fun _ => S.positive) q hq residue
        (fun _ => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize)).mean
        (fun v => φ (allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => (v j none : ℝ) / S.value))) -
      ∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
        ∂unitBoxMeasure Input| ≤
      (2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value) := by
  classical
  intro lower width K
  have he := allocatedOriginalSampleFullSlice_residue_riemann B U basis hR hσ S x u
    sample hs ht hσbound (fun _ => 1) (fun _ => S.value) (fun _ => q) (fun _ => 0)
    (fun _ => Nat.zero_lt_one) (fun _ => hS) (δ := 1) zero_lt_one
    (fun _ => fullIntervalProgression_subset S.value)
    (fun _ => by simp only [Nat.cast_one, fullIntervalProgression_card, one_mul, le_refl])
    (fun _ _ => q) residue (fun _ _ => hq) (fun _ _ => le_rfl)
    (fun _ => hsize) (fun _ => hsmall)
    (ε := 1 / S.value) (by positivity) (fun _ => by simp only [Nat.cast_one, le_refl])
    φ hφ hφone
  simpa only [principalResidueWeights, Int.cast_zero, Nat.cast_one, zero_add,
    one_mul, zero_div, lower, width, K] using he

include hR hσ in
theorem allocatedOriginalSampleFullSlice_full_residue_complex_riemann
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (hS : 2 ≤ S.value) (q : ℕ) (hq : 0 < q)
    (residue : Input → Option Empty → ZMod q)
    (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (φ : (Output → ℝ) → ℂ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    ‖(principalResidueWeights (fun a : Active => B a.val) (fun a : Active => degree a.val)
        (fun _ => S.value) (fun _ => S.positive) q hq residue
        (fun _ => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize)).complexMean
        (fun v => φ (allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => (v j none : ℝ) / S.value))) -
      ∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
        ∂unitBoxMeasure Input‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) := by
  classical
  intro lower width K
  let p := (principalResidueWeights (fun a : Active => B a.val) (fun a : Active => degree a.val)
        (fun _ => S.value) (fun _ => S.positive) q hq residue
        (fun _ => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize))
  let F := allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1) sample
  let g := fun y => φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
  have hig : Integrable g (unitBoxMeasure Input) :=
    ⟨(hφ.continuous.measurable.comp
      (allocatedOriginalSampleFullSliceMap_measurable B U basis S x u lower width sample)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall (fun y => hφone _))⟩
  have hφre : LipschitzWith Kφ (fun y => (φ y).re) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [Real.dist_eq, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans (by simpa only [dist_eq_norm] using hφ.dist_le_mul v w)
  have hφim : LipschitzWith Kφ (fun y => (φ y).im) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [Real.dist_eq, ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans (by simpa only [dist_eq_norm] using hφ.dist_le_mul v w)
  have hre := allocatedOriginalSampleFullSlice_full_residue_real_riemann B U basis hR hσ S x u
    sample hs ht hσbound hS q hq residue hsize hsmall (fun y => (φ y).re) hφre
    (fun y => (Complex.abs_re_le_norm _).trans (hφone y))
  have him := allocatedOriginalSampleFullSlice_full_residue_real_riemann B U basis hR hσ S x u
    sample hs ht hσbound hS q hq residue hsize hsmall (fun y => (φ y).im) hφim
    (fun y => (Complex.abs_im_le_norm _).trans (hφone y))
  have hgre : (∫ y, g y ∂unitBoxMeasure Input).re = ∫ y, (g y).re ∂unitBoxMeasure Input := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hig).symm
  have hgim : (∫ y, g y ∂unitBoxMeasure Input).im = ∫ y, (g y).im ∂unitBoxMeasure Input := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im hig).symm
  change ‖p.complexMean (fun v => φ (F (fun j => (v j none : ℝ) / S.value))) -
    ∫ y, g y ∂unitBoxMeasure Input‖ ≤ _
  calc
    _ ≤ |(p.complexMean (fun v => φ (F (fun j => (v j none : ℝ) / S.value))) -
        ∫ y, g y ∂unitBoxMeasure Input).re| +
      |(p.complexMean (fun v => φ (F (fun j => (v j none : ℝ) / S.value))) -
        ∫ y, g y ∂unitBoxMeasure Input).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) := by
      apply add_le_add
      · rw [Complex.sub_re, FiniteProbabilityWeights.complexMean_re, hgre]
        exact hre
      · rw [Complex.sub_im, FiniteProbabilityWeights.complexMean_im, hgim]
        exact him
    _ = _ := by ring

include hR hσ in
theorem allocatedOriginalSample_full_residue_perturbed_riemann
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (hS : 2 ≤ S.value) (q : ℕ) (hq : 0 < q)
    (residue : Input → Option Empty → ZMod q)
    (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (b : ∀ a : Active, B a.val)
    {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (1 / 2) A η)
    (φ : (Output → ℝ) → ℂ) {Kφ : ℝ≥0}
    (hφ : LipschitzWith Kφ φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    ‖(principalResidueWeights (fun a : Active => B a.val) (fun a : Active => degree a.val)
        (fun _ => S.value) (fun _ => S.positive) q hq residue
        (fun _ => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize)).complexMean
        (fun v => φ (fun o =>
          MvPolynomial.eval (allocatedOriginalSampleSliceInput B U basis S x u
            (fun _ _ => 0) (fun _ _ => 1) (fun j => (v j none : ℝ) / S.value))
            (monomialArrayPolynomial Subtype.val
              (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val)) / R o.1.val.1)) -
      ∫ y, φ (allocatedOriginalSampleLiftMap B U basis S lower width sample y)
        ∂unitBoxMeasure Input‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η := by
  classical
  intro lower width K
  have hSreal : (2 : ℝ) ≤ S.value := by exact_mod_cast hS
  have hSpos : (0 : ℝ) < S.value := by exact_mod_cast S.positive
  have hw0 : 0 ≤ ((S.value : ℝ) - 1) / S.value :=
    div_nonneg (by linarith) hSpos.le
  have hw1 : ((S.value : ℝ) - 1) / S.value ≤ 1 := by
    apply (div_le_one hSpos).mpr
    linarith
  have hw2 : (1 / 2 : ℝ) ≤ ((S.value : ℝ) - 1) / S.value := by
    apply (le_div_iff₀ hSpos).mpr
    linarith
  have hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1 := by
    intro a p
    simpa only [lower, width, abs_zero, zero_add, abs_of_nonneg hw0] using hw1
  have hp := allocatedOriginalSample_slice_complex_perturbation B U basis hR hσ S x u lower width
    sample hs hwidth b (δ := 1 / 2) (by norm_num) (by norm_num) hη
    (fun _ _ => hw2) (fun _ _ => le_rfl) A hA ht hσbound htail φ hφ.continuous.measurable hφone
  have hq' := allocatedOriginalSampleFullSlice_full_residue_complex_riemann
    B U basis hR hσ S x u sample hs ht hσbound hS q hq residue hsize hsmall φ hφ hφone
  let p := (principalResidueWeights (fun a : Active => B a.val) (fun a : Active => degree a.val)
        (fun _ => S.value) (fun _ => S.positive) q hq residue
        (fun _ => by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize))
  let f := fun (v : Input → IntegerScalarCubeBox Empty S.value) => φ (allocatedOriginalSampleFullSliceMap B U basis S x u
    (fun _ _ => 0) (fun _ _ => 1) sample (fun j => (v j none : ℝ) / S.value))
  have he : ‖p.complexMean f -
      ∫ y, φ (allocatedOriginalSampleLiftMap B U basis S lower width sample y) ∂unitBoxMeasure Input‖ ≤
      2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
        ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η := by
    calc
      _ ≤ ‖p.complexMean f -
          ∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y) ∂unitBoxMeasure Input‖ +
        ‖(∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y) ∂unitBoxMeasure Input) -
          ∫ y, φ (allocatedOriginalSampleLiftMap B U basis S lower width sample y) ∂unitBoxMeasure Input‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add hq' (by simpa only [norm_sub_rev] using hp)
  have hmap : allocatedOriginalSampleFullSliceMap B U basis S x u
      (fun _ _ => 0) (fun _ _ => 1) sample = fun y o =>
        MvPolynomial.eval (allocatedOriginalSampleSliceInput B U basis S x u
          (fun _ _ => 0) (fun _ _ => 1) y)
          (monomialArrayPolynomial Subtype.val
            (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val)) / R o.1.val.1 := by
    funext y o
    exact allocatedOriginalSampleFullSliceMap_eq_eval B U basis S x u
      (fun _ _ => 0) (fun _ _ => 1) sample y o
  simpa only [p, f, hmap] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)

omit hR hσ [DecidableEq G] in
theorem allocatedFixedSpatialKernelMap_lipschitz
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1) :
    LipschitzWith 1 (fixedSpatialKernelMap budget (S.value : ℝ) z) := by
  apply (fixedSpatialKernelMap_lipschitz budget (S.value : ℝ) z hz).weaken
  change (Fintype.card G : ℝ) * ‖(S.value : ℝ) / (1 + budget)‖ ≤ 1
  simpa only [Real.norm_eq_abs] using allocatedKernelSlowBudget_abs_le_one B U basis S

omit hR hσ in
theorem allocatedFixedPath_kernel_residue_riemann
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (sample : Sample)
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (φ : (G → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ r, LipschitzWith Kφ (φ r)) (hbound : ∀ r y, ‖φ r y‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)).complexMean
        (fun x => ∫ v, φ (fun g => ((x g none : ℤ) : ZMod q))
          (fixedSpatialKernelMap budget (S.value : ℝ) z (fun g => (x g none : ℝ) / S.value),
            allocatedOriginalSampleLiftMap B U basis S lower width sample v) ∂unitBoxMeasure Input) -
      (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun r =>
        ∫ k, ∫ v, φ r (fixedSpatialKernelMap budget (S.value : ℝ) z k,
          allocatedOriginalSampleLiftMap B U basis S lower width sample v)
          ∂unitBoxMeasure Input ∂unitBoxMeasure G)‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
        (Fintype.card G * ((q : ℝ) / S.value)) := by
  classical
  let F := fun (r : G → ZMod q) (k : G → ℝ) =>
    ∫ v, φ r (fixedSpatialKernelMap budget (S.value : ℝ) z k,
      allocatedOriginalSampleLiftMap B U basis S lower width sample v) ∂unitBoxMeasure Input
  have hF (r : G → ZMod q) : LipschitzWith Kφ (F r) := by
    simpa only [mul_one, Function.comp_def, F] using
      (allocatedOriginalSampleForecastPartial_lipschitz B U basis S lower width sample
        (φ r) (hφ r) (hbound r)).comp
          (allocatedFixedSpatialKernelMap_lipschitz B U basis S z hz)
  have hFb (r : G → ZMod q) (k : G → ℝ) : ‖F r k‖ ≤ 1 :=
    allocatedOriginalSampleForecastPartial_norm_le B U basis S lower width sample
      (φ r) (hbound r) _
  have hproject : LipschitzWith 1 (fun k : G → Option Empty → ℝ => fun g => k g none) := by
    apply LipschitzWith.of_dist_le_mul
    intro k l
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro g
    exact (dist_le_pi_dist (k g) (l g) none).trans (dist_le_pi_dist k l g)
  have he := originalKernel_residue_slow_quadrature S.value q S.positive (NeZero.pos q) hsize
    (by simpa only [Measure.real, scalarCubeDomain_empty_volume, ENNReal.toReal_one] using hsmall)
    (fun r k => F r (fun g => k g none))
    (fun r => by simpa only [mul_one, Function.comp_def] using (hF r).comp hproject)
    (fun r k => hFb r _)
  have hid (r : G → ZMod q) :
      (∫ k, F r (fun g => k g none) ∂scalarCubeProductMeasure G Empty) =
        ∫ k, F r k ∂unitBoxMeasure G := by
    rw [← scalarCubeProductMeasure_empty_map G]
    exact (integral_map (by fun_prop : Measurable (fun k : G → Option Empty → ℝ => fun g => k g none)).aemeasurable
      (hF r).continuous.measurable.aestronglyMeasurable).symm
  simpa only [F, hid, FiniteProbabilityWeights.uniform_complexMean, Measure.real,
    scalarCubeDomain_empty_volume, ENNReal.toReal_one, div_one] using he

include hR hσ in
theorem allocatedFixedPath_joint_residue_riemann
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (u : PrincipalAxisTuples (α := Empty)
      (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (b : ∀ a : Active, B a.val) {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (1 / 2) A η)
    (hS : 2 ≤ S.value) (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (φ : (G → ZMod q) → (Input → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ rG rA, LipschitzWith Kφ (φ rG rA))
    (hbound : ∀ rG rA y, ‖φ rG rA y‖ ≤ 1) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)
    let active := FiniteProbabilityWeights.pi (fun _ : Input => integerScalarCubeWeights Empty S.value S.positive)
    ‖kernel.complexMean (fun x => active.complexMean (fun v =>
        φ (fun g => ((x g none : ℤ) : ZMod q)) (fun j => ((v j none : ℤ) : ZMod q))
          (fixedSpatialKernelMap budget (S.value : ℝ) z (fun g => (x g none : ℝ) / S.value),
            allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
              sample (fun j => (v j none : ℝ) / S.value)))) -
      (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun rA =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          ∫ k, ∫ v, φ rG rA (fixedSpatialKernelMap budget (S.value : ℝ) z k,
            allocatedOriginalSampleLiftMap B U basis S lower width sample v)
            ∂unitBoxMeasure Input ∂unitBoxMeasure G))‖ ≤
      ((Fintype.card Input : ℝ) * ((q : ℝ) / S.value) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
        (Fintype.card G * ((q : ℝ) / S.value)) := by
  classical
  intro lower width K kernel active
  let residues := FiniteProbabilityWeights.uniform (Input → ZMod q)
  let E := 2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
    ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η
  let EA := (Fintype.card Input : ℝ) * ((q : ℝ) / S.value) + E
  let EG := (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
    (Fintype.card G * ((q : ℝ) / S.value))
  let value := fun (x : G → IntegerScalarCubeBox Empty S.value) (rA : Input → ZMod q)
      (v : Input → IntegerScalarCubeBox Empty S.value) =>
    φ (fun g => ((x g none : ℤ) : ZMod q)) rA
      (fixedSpatialKernelMap budget (S.value : ℝ) z (fun g => (x g none : ℝ) / S.value),
        allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
          sample (fun j => (v j none : ℝ) / S.value))
  let reference := fun (x : G → IntegerScalarCubeBox Empty S.value) (rA : Input → ZMod q) =>
    ∫ v, φ (fun g => ((x g none : ℤ) : ZMod q)) rA
      (fixedSpatialKernelMap budget (S.value : ℝ) z (fun g => (x g none : ℝ) / S.value),
        allocatedOriginalSampleLiftMap B U basis S lower width sample v) ∂unitBoxMeasure Input
  let conditioned := fun rA : Input → ZMod q =>
    FiniteProbabilityWeights.pi (fun j : Input => scalarCubeResidueWeights Empty S.value q S.positive
      (fun _ => q) (fun _ => rA j) (fun _ => NeZero.pos q) (fun _ => le_rfl)
      (by simpa only [Fintype.card_empty, zero_add, one_mul] using hsize))
  have hcond (x : G → IntegerScalarCubeBox Empty S.value) (rA : Input → ZMod q) :
      ‖(conditioned rA).complexMean (value x rA) - reference x rA‖ ≤ E := by
    let test := fun w : Output → ℝ => φ (fun g => ((x g none : ℤ) : ZMod q)) rA
      (fixedSpatialKernelMap budget (S.value : ℝ) z (fun g => (x g none : ℝ) / S.value), w)
    have htest : LipschitzWith Kφ test := by
      apply LipschitzWith.of_dist_le_mul
      intro v w
      simpa only [test, Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using
        (hφ (fun g => ((x g none : ℤ) : ZMod q)) rA).dist_le_mul
          (fixedSpatialKernelMap budget (S.value : ℝ) z (fun g => (x g none : ℝ) / S.value), v)
          (fixedSpatialKernelMap budget (S.value : ℝ) z (fun g => (x g none : ℝ) / S.value), w)
    have he := allocatedOriginalSample_full_residue_perturbed_riemann B U basis hR hσ S x u
      sample hs ht hσbound hS q (NeZero.pos q) (fun j _ => rA j) hsize hsmall b hη A hA htail
      test htest (fun w => hbound _ _ _)
    have hmap : allocatedOriginalSampleFullSliceMap B U basis S x u
        (fun _ _ => 0) (fun _ _ => 1) sample = fun y o =>
          MvPolynomial.eval (allocatedOriginalSampleSliceInput B U basis S x u
            (fun _ _ => 0) (fun _ _ => 1) y)
            (monomialArrayPolynomial Subtype.val
              (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val)) / R o.1.val.1 := by
      funext y o
      exact allocatedOriginalSampleFullSliceMap_eq_eval B U basis S x u
        (fun _ _ => 0) (fun _ _ => 1) sample y o
    simpa only [conditioned, value, reference, E, K, lower, width, test,
      principalResidueWeights, hmap] using he
  have hprincipal (x : G → IntegerScalarCubeBox Empty S.value) :
      ‖active.complexMean (fun v => value x (fun j => ((v j none : ℤ) : ZMod q)) v) -
        residues.complexMean (reference x)‖ ≤ EA := by
    have hmix := integerScalarCubeWeights_empty_pi_uniform_residue_error
      S.value q S.positive (NeZero.pos q) hsize (value x) (fun rA v => hbound _ _ _)
    have havg : ‖residues.complexMean (fun rA => (conditioned rA).complexMean (value x rA)) -
        residues.complexMean (reference x)‖ ≤ E :=
      (residues.norm_complexMean_sub_le _ _ (fun _ => E) (fun rA _ => hcond x rA)).trans_eq
        (residues.mean_const E)
    have hmix' : ‖active.complexMean (fun v => value x (fun j => ((v j none : ℤ) : ZMod q)) v) -
        residues.complexMean (fun rA => (conditioned rA).complexMean (value x rA))‖ ≤
        (Fintype.card Input : ℝ) * ((q : ℝ) / S.value) := by
      simpa only [active, residues, conditioned, FiniteProbabilityWeights.uniform_complexMean] using hmix
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hmix' havg)
  have hfirst := (kernel.norm_complexMean_sub_le _ _ (fun _ => EA)
    (fun x _ => hprincipal x)).trans_eq (kernel.mean_const EA)
  have hlast := (residues.norm_complexMean_sub_le _ _ (fun _ => EG)
    (fun rA _ => allocatedFixedPath_kernel_residue_riemann B U basis S z hz sample lower width
      q hsize hsmall (fun rG => φ rG rA) (fun rG => hφ rG rA) (fun rG => hbound rG rA))).trans_eq
    (residues.mean_const EG)
  rw [← FiniteProbabilityWeights.complexMean_commute kernel residues] at hlast
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hfirst hlast)

include hR hσ in
theorem allocatedFixedPath_joint_residue_weighted_riemann
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (u : PrincipalAxisTuples (α := Empty)
      (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (b : ∀ a : Active, B a.val) {η : ℝ} (hη : 0 < η)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (htail : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) (1 / 2) A η)
    (hS : 2 ≤ S.value) (q : ℕ) [NeZero q] (hsize : q ≤ S.value)
    (hsmall : scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / S.value) < 1)
    (coefficient : (G → ZMod q) → (Input → ZMod q) → ℂ)
    (hcoefficient : ∀ rG rA, ‖coefficient rG rA‖ ≤ 1)
    (φ : (G → ZMod q) → (Input → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ rG rA, LipschitzWith Kφ (φ rG rA))
    (hbound : ∀ rG rA y, ‖φ rG rA y‖ ≤ 1) :
    let lower := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) => (0 : ℝ)
    let width := fun (_a : Active) (_p : B _a.val × Fin (degree _a.val)) =>
      ((S.value : ℝ) - 1) / S.value
    let K := Kφ * allocatedOriginalSampleFullSliceLip B U basis S t
    let kernel := FiniteProbabilityWeights.pi (fun _ : G => integerScalarCubeWeights Empty S.value S.positive)
    let active := FiniteProbabilityWeights.pi (fun _ : Input => integerScalarCubeWeights Empty S.value S.positive)
    ‖kernel.complexMean (fun x => active.complexMean (fun v =>
        coefficient (fun g => ((x g none : ℤ) : ZMod q)) (fun j => ((v j none : ℤ) : ZMod q)) *
        φ (fun g => ((x g none : ℤ) : ZMod q)) (fun j => ((v j none : ℤ) : ZMod q))
          (fixedSpatialKernelMap budget (S.value : ℝ) z (fun g => (x g none : ℝ) / S.value),
            allocatedOriginalSampleFullSliceMap B U basis S x u (fun _ _ => 0) (fun _ _ => 1)
              sample (fun j => (v j none : ℝ) / S.value)))) -
      (FiniteProbabilityWeights.uniform (Input → ZMod q)).complexMean (fun rA =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          coefficient rG rA * ∫ k, ∫ v, φ rG rA (fixedSpatialKernelMap budget (S.value : ℝ) z k,
            allocatedOriginalSampleLiftMap B U basis S lower width sample v)
            ∂unitBoxMeasure Input ∂unitBoxMeasure G))‖ ≤
      ((Fintype.card Input : ℝ) * ((q : ℝ) / S.value) +
        (2 * ((2 * scalarCubeGridBoundaryConstant Empty + K * 2) *
          ∑ _j : Input, (q : ℝ) / S.value + K * (1 / S.value)) + 2 * η)) +
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ)) *
        (Fintype.card G * ((q : ℝ) / S.value)) := by
  have hmul (rG : G → ZMod q) (rA : Input → ZMod q) :
      LipschitzWith Kφ (fun y => coefficient rG rA * φ rG rA y) := by
    apply LipschitzWith.of_dist_le_mul
    intro y w
    rw [dist_eq_norm, ← mul_sub, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hcoefficient rG rA)).trans
      (by simpa only [dist_eq_norm] using (hφ rG rA).dist_le_mul y w)
  have hb (rG : G → ZMod q) (rA : Input → ZMod q) (y : Domain) :
      ‖coefficient rG rA * φ rG rA y‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hcoefficient rG rA)).trans
      (hbound rG rA y)
  simpa only [integral_const_mul] using
    allocatedFixedPath_joint_residue_riemann B U basis hR hσ S z hz u sample hs
      ht hσbound b hη A hA htail hS q hsize hsmall
      (fun rG rA y => coefficient rG rA * φ rG rA y) hmul hb

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)
local notation "Domain" => (Spatial × (Output → ℝ))
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "ShortTuple" => PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)

omit hR hσ in
theorem allocatedFixedPath_sliced_kernel_residue_riemann
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1)
    (sample : Sample)
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (H : G → ℕ) (hH : ∀ g, 0 < H g) (start : G → ℤ)
    (step : ℕ) (hstep : 0 < step)
    (hcontained : ∀ g, integerProgressionSupport (start g) (step : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (q : ℕ) [NeZero q] (hsize : ∀ g, q ≤ H g)
    (hsmall : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H g) < 1)
    (φ : (G → ZMod q) → Domain → ℂ) {Kφ : ℝ≥0}
    (hφ : ∀ r, LipschitzWith Kφ (φ r)) (hbound : ∀ r y, ‖φ r y‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (H g) (hH g))).complexMean
        (fun x => ∫ v, φ (fun g => ((start g + (step : ℤ) * (x g none : ℤ) : ℤ) : ZMod q))
          (fixedSpatialKernelMap budget (S.value : ℝ) z
            (fun g => ((start g : ℝ) + (step : ℝ) * (x g none : ℝ)) / S.value),
            allocatedOriginalSampleLiftMap B U basis S lower width sample v) ∂unitBoxMeasure Input) -
      (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun r =>
        ∫ k, ∫ v, φ (fun g => (start g : ZMod q) + (step : ZMod q) * r g)
          (fixedSpatialKernelMap budget (S.value : ℝ) z
            (fun g => ((start g : ℝ) + (step : ℝ) * ((H g - 1 : ℕ) : ℝ) * k g) / S.value),
            allocatedOriginalSampleLiftMap B U basis S lower width sample v)
          ∂unitBoxMeasure Input ∂unitBoxMeasure G)‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty + Kφ) + Kφ) *
        ∑ g, (q : ℝ) / H g := by
  classical
  let F := fun (r : G → ZMod q) (k : G → ℝ) =>
    ∫ v, φ r (fixedSpatialKernelMap budget (S.value : ℝ) z k,
      allocatedOriginalSampleLiftMap B U basis S lower width sample v) ∂unitBoxMeasure Input
  have hF (r : G → ZMod q) : LipschitzWith Kφ (F r) := by
    simpa only [mul_one, Function.comp_def, F] using
      (allocatedOriginalSampleForecastPartial_lipschitz B U basis S lower width sample
        (φ r) (hφ r) (hbound r)).comp
          (allocatedFixedSpatialKernelMap_lipschitz B U basis S z hz)
  have hFb (r : G → ZMod q) (k : G → ℝ) : ‖F r k‖ ≤ 1 :=
    allocatedOriginalSampleForecastPartial_norm_le B U basis S lower width sample
      (φ r) (hbound r) _
  have hspan := affineKernel_span_of_contained H hH start step S.value hstep hcontained
  have he := affineKernel_residue_slow_quadrature H q hH (NeZero.pos q) hsize
    (fun g => by simpa only [Measure.real, scalarCubeDomain_empty_volume, ENNReal.toReal_one] using hsmall g)
    (fun g => (start g : ℝ)) (step : ℝ) (S.value : ℝ) (by exact_mod_cast S.positive)
    (Nat.cast_nonneg _) hspan
    (fun r g => (start g : ZMod q) + (step : ZMod q) * r g) F hF hFb
  have hid (r : G → ZMod q) :
      (∫ k, F (fun g => (start g : ZMod q) + (step : ZMod q) * r g)
        (affineKernelContinuousPoint (fun g => (start g : ℝ)) (step : ℝ) (S.value : ℝ) H k)
        ∂scalarCubeProductMeasure G Empty) =
      ∫ k, F (fun g => (start g : ZMod q) + (step : ZMod q) * r g)
        (fun g => ((start g : ℝ) + (step : ℝ) * ((H g - 1 : ℕ) : ℝ) * k g) / S.value)
        ∂unitBoxMeasure G := by
    rw [← scalarCubeProductMeasure_empty_map G]
    exact (integral_map (by fun_prop : Measurable
        (fun k : G → Option Empty → ℝ => fun g => k g none)).aemeasurable
      (show AEStronglyMeasurable (fun k : G → ℝ =>
        F (fun g => (start g : ZMod q) + (step : ZMod q) * r g)
          (fun g => ((start g : ℝ) + (step : ℝ) * ((H g - 1 : ℕ) : ℝ) * k g) / S.value))
          ((scalarCubeProductMeasure G Empty).map (fun k => fun g => k g none)) from
        ((hF _).continuous.comp (by fun_prop)).measurable.aestronglyMeasurable)).symm
  simpa only [hid, F, FiniteProbabilityWeights.uniform_complexMean, Measure.real,
    scalarCubeDomain_empty_volume, ENNReal.toReal_one, div_one,
    Int.cast_add, Int.cast_mul, Int.cast_natCast] using he

end Erdos3.VectorPolynomial

end

end OAI
