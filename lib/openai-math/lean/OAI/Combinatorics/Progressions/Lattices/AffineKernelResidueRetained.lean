import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Lattices.OriginalKernelResidueRetained

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem originalKernel_residue_slow_quadrature_varying
    {G : Type*} [Fintype G] [DecidableEq G]
    (L : G → ℕ) (q : ℕ) [NeZero q]
    (hL : ∀ g, 0 < L g) (hq : 0 < q) (hqL : ∀ g, q ≤ L g)
    (hsmall : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / L g) <
      volume.real (scalarCubeDomain Empty))
    (F : (G → ZMod q) → (G → Option Empty → ℝ) → ℂ)
    {K : ℝ≥0} (hF : ∀ r, LipschitzWith K (F r))
    (hbound : ∀ r x, ‖F r x‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))).complexMean
        (fun z => F (fun g => ((z g none : ℤ) : ZMod q))
          (fun g i => (z g i : ℝ) / L g)) -
      𝔼 r : G → ZMod q, ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty /
        volume.real (scalarCubeDomain Empty) + K)) *
          (∑ g, (q : ℝ) / L g) := by
  let test := fun (r : G → ZMod q) (z : ∀ g, IntegerScalarCubeBox Empty (L g)) =>
    F r (fun g i => (z g i : ℝ) / L g)
  let law := fun (r : G → ZMod q) => FiniteProbabilityWeights.pi
    (fun g : G => scalarCubeResidueWeights Empty (L g) q (hL g)
      (fun _ => q) (fun _ => r g) (fun _ => hq) (fun _ => le_rfl) (by simpa using hqL g))
  let e : ℝ := 2 * (2 * scalarCubeGridBoundaryConstant Empty /
    volume.real (scalarCubeDomain Empty) + K) * (∑ g, (q : ℝ) / L g)
  have hcond (r : G → ZMod q) :
      ‖(law r).complexMean (test r) - ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ ≤ e := by
    simpa only [law, test, e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      scalarCubeResidueWeights_pi_complex_riemann L (fun _ => q) hL
        (fun (_ : G) (_ : Option Empty) => q) (fun g _ => r g) (fun _ _ => hq)
        (fun _ _ => le_rfl) (fun g => by simpa using hqL g)
        hsmall (F r) (hF r) zero_le_one (hbound r)
  have hmix := integerScalarCubeWeights_empty_pi_uniform_residue_error_varying L q hL hq hqL
    test (fun r z => hbound r _)
  have havg : ‖(𝔼 r : G → ZMod q, (law r).complexMean (test r)) -
      𝔼 r : G → ZMod q, ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ ≤ e := by
    rw [← Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    exact (Finset.expect_le_expect (fun r _ => hcond r)).trans_eq (by simp)
  calc
    _ ≤ ‖(FiniteProbabilityWeights.pi (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))).complexMean
        (fun z => test (fun g => ((z g none : ℤ) : ZMod q)) z) -
          𝔼 r : G → ZMod q, (law r).complexMean (test r)‖ +
        ‖(𝔼 r : G → ZMod q, (law r).complexMean (test r)) -
          𝔼 r : G → ZMod q, ∫ x, F r x ∂scalarCubeProductMeasure G Empty‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (∑ g, (q : ℝ) / L g) + e := add_le_add hmix havg
    _ = _ := by dsimp only [e]; ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {G R : Type*} [Fintype G] [DecidableEq G]

theorem affineKernel_residue_slow_quadrature
    (H : G → ℕ) (q : ℕ) [NeZero q] (hH : ∀ g, 0 < H g)
    (hq : 0 < q) (hqH : ∀ g, q ≤ H g)
    (hsmall : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H g) <
      volume.real (scalarCubeDomain Empty))
    (lower : G → ℝ) (step S : ℝ) (hS : 0 < S) (hstep : 0 ≤ step)
    (hspan : ∀ g, step * ((H g - 1 : ℕ) : ℝ) ≤ S)
    (residueMap : (G → ZMod q) → R) (F : R → (G → ℝ) → ℂ)
    {K : ℝ≥0} (hF : ∀ r, LipschitzWith K (F r))
    (hbound : ∀ r x, ‖F r x‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (H g) (hH g))).complexMean
        (fun z => F (residueMap (fun g => ((z g none : ℤ) : ZMod q)))
          (fun g => (lower g + step * (z g none : ℝ)) / S)) -
      𝔼 r : G → ZMod q, ∫ x,
        F (residueMap r) (affineKernelContinuousPoint lower step S H x)
          ∂scalarCubeProductMeasure G Empty‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty /
        volume.real (scalarCubeDomain Empty) + K) + K) * ∑ g, (q : ℝ) / H g := by
  let p := FiniteProbabilityWeights.pi
    (fun g => integerScalarCubeWeights Empty (H g) (hH g))
  let test := fun r x => F (residueMap r) (affineKernelContinuousPoint lower step S H x)
  have htest (r : G → ZMod q) : LipschitzWith K (test r) := by
    simpa only [test, Function.comp_def, mul_one] using (hF (residueMap r)).comp
      (affineKernelContinuousPoint_lipschitz lower step S H hS hstep hspan)
  have hquad := originalKernel_residue_slow_quadrature_varying H q hH hq hqH
    hsmall test htest (fun r x => hbound _ _)
  have hsum : (∑ g, (1 : ℝ) / H g) ≤ ∑ g, (q : ℝ) / H g := by
    apply Finset.sum_le_sum
    intro g _
    exact div_le_div_of_nonneg_right (by exact_mod_cast hq) (by positivity)
  have hpoint :
      ‖p.complexMean (fun z => F (residueMap (fun g => ((z g none : ℤ) : ZMod q)))
          (fun g => (lower g + step * (z g none : ℝ)) / S)) -
        p.complexMean (fun z => test (fun g => ((z g none : ℤ) : ZMod q))
          (fun g i => (z g i : ℝ) / H g))‖ ≤ (K : ℝ) * ∑ g, (q : ℝ) / H g := by
    apply (p.norm_complexMean_sub_le _ _ (fun _ => (K : ℝ) * ∑ g, (q : ℝ) / H g) ?_).trans_eq
      (p.mean_const _)
    intro z hz
    rw [← dist_eq_norm]
    exact ((hF _).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
      ((affineKernelEndpoint_dist_le lower step S H hH hS hstep hspan z hz).trans hsum)
      K.coe_nonneg)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add hpoint hquad).trans_eq (by ring))

theorem affineKernel_integer_residue_slow_quadrature
    (H : G → ℕ) (q : ℕ) [NeZero q] (hH : ∀ g, 0 < H g)
    (hq : 0 < q) (hqH : ∀ g, q ≤ H g)
    (hsmall : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H g) <
      volume.real (scalarCubeDomain Empty))
    (start : G → ℤ) (step : ℤ) (S : ℝ) (hS : 0 < S) (hstep : 0 ≤ step)
    (hspan : ∀ g, (step : ℝ) * ((H g - 1 : ℕ) : ℝ) ≤ S)
    (F : (G → ZMod q) → (G → ℝ) → ℂ)
    {K : ℝ≥0} (hF : ∀ r, LipschitzWith K (F r))
    (hbound : ∀ r x, ‖F r x‖ ≤ 1) :
    ‖(FiniteProbabilityWeights.pi (fun g => integerScalarCubeWeights Empty (H g) (hH g))).complexMean
        (fun z => F (fun g => ((start g + step * (z g none : ℤ) : ℤ) : ZMod q))
          (fun g => ((start g + step * (z g none : ℤ) : ℤ) : ℝ) / S)) -
      𝔼 r : G → ZMod q, ∫ x,
        F (fun g => (start g : ZMod q) + (step : ZMod q) * r g)
          (fun g => ((start g : ℝ) + (step : ℝ) * ((H g - 1 : ℕ) : ℝ) * x g none) / S)
          ∂scalarCubeProductMeasure G Empty‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty /
        volume.real (scalarCubeDomain Empty) + K) + K) * ∑ g, (q : ℝ) / H g := by
  have h := affineKernel_residue_slow_quadrature H q hH hq hqH hsmall
      (fun g => (start g : ℝ)) (step : ℝ) S hS (by exact_mod_cast hstep) hspan
      (fun r g => (start g : ZMod q) + (step : ZMod q) * r g) F hF hbound
  simp only [Int.cast_add, Int.cast_mul] at ⊢
  convert h using 1
  rfl

omit [Fintype G] [DecidableEq G] in

theorem affineKernel_span_of_contained
    (H : G → ℕ) (hH : ∀ g, 0 < H g) (start : G → ℤ)
    (step S : ℕ) (hstep : 0 < step)
    (hcontained : ∀ g, integerProgressionSupport (start g) (step : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S : ℤ)) :
    ∀ g, (step : ℝ) * ((H g - 1 : ℕ) : ℝ) ≤ S := by
  intro g
  have hfirst := hcontained g
    (integerProgressionSupport_point (start g) step (H g) hstep 0 (hH g))
  have hlast := hcontained g
    (integerProgressionSupport_point (start g) step (H g) hstep (H g - 1) (by
      have := hH g
      omega))
  have hc : (0 : ℤ) ≤ start g := by simpa using (Finset.mem_Ico.mp hfirst).1
  have he : start g + (step : ℤ) * ((H g - 1 : ℕ) : ℤ) < S :=
    (Finset.mem_Ico.mp hlast).2
  have hs : (step : ℤ) * ((H g - 1 : ℕ) : ℤ) ≤ S := by omega
  exact_mod_cast hs

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem originalKernel_residue_slow_retained_quadrature_varying
    {G Z : Type*} [Fintype G] [DecidableEq G] [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (L : G → ℕ) (q : ℕ) [NeZero q] (hL : ∀ g, 0 < L g) (hq : 0 < q)
    (hqL : ∀ g, q ≤ L g)
    (hsmall : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / L g) <
      volume.real (scalarCubeDomain Empty))
    (F : Z → (G → ZMod q) → (G → Option Empty → ℝ) → ℂ)
    (hMeas : ∀ r, Measurable (fun zx : Z × (G → Option Empty → ℝ) => F zx.1 r zx.2))
    {K : ℝ≥0} (hLip : ∀ z r, LipschitzWith K (F z r))
    (hbound : ∀ z r x, ‖F z r x‖ ≤ 1) :
    ‖(∫ z, (FiniteProbabilityWeights.pi
        (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))).complexMean
          (fun y => F z (fun g => ((y g none : ℤ) : ZMod q))
            (fun g i => (y g i : ℝ) / L g)) ∂μ) -
      ∫ z, 𝔼 r : G → ZMod q,
        ∫ x, F z r x ∂scalarCubeProductMeasure G Empty ∂μ‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty /
        volume.real (scalarCubeDomain Empty) + K)) *
          (∑ g, (q : ℝ) / L g) := by
  let p := FiniteProbabilityWeights.pi
    (fun g : G => integerScalarCubeWeights Empty (L g) (hL g))
  let a (z : Z) := p.complexMean
    (fun y => F z (fun g => ((y g none : ℤ) : ZMod q))
      (fun g i => (y g i : ℝ) / L g))
  let b (z : Z) := 𝔼 r : G → ZMod q,
    ∫ x, F z r x ∂scalarCubeProductMeasure G Empty
  have haMeas : Measurable a := by
    unfold a FiniteProbabilityWeights.complexMean
    apply Finset.measurable_sum
    intro y _
    exact measurable_const.mul ((hMeas _).comp (measurable_id.prodMk measurable_const))
  have haBound (z : Z) : ‖a z‖ ≤ 1 := by
    apply (p.norm_complexMean_le_mean_norm _).trans
    exact (p.mean_mono (fun y => hbound z _ _)).trans_eq (p.mean_const 1)
  have haInt : Integrable a μ :=
    (integrable_const (1 : ℝ)).mono' haMeas.aestronglyMeasurable (ae_of_all μ haBound)
  have hiMeas (r : G → ZMod q) :
      StronglyMeasurable (fun z => ∫ x, F z r x ∂scalarCubeProductMeasure G Empty) :=
    (hMeas r).stronglyMeasurable.integral_prod_right'
  have hiBound (z : Z) (r : G → ZMod q) :
      ‖∫ x, F z r x ∂scalarCubeProductMeasure G Empty‖ ≤ 1 := by
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const
        (ae_of_all (scalarCubeProductMeasure G Empty) (hbound z r))
  have hbMeas : Measurable b := by
    unfold b
    simp only [Fintype.expect_eq_sum_div_card]
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun r _ => (hiMeas r).measurable)
  have hbBound (z : Z) : ‖b z‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    exact (Finset.expect_le_expect (fun r _ => hiBound z r)).trans_eq (by simp)
  have hbInt : Integrable b μ :=
    (integrable_const (1 : ℝ)).mono' hbMeas.aestronglyMeasurable (ae_of_all μ hbBound)
  change ‖(∫ z, a z ∂μ) - ∫ z, b z ∂μ‖ ≤ _
  rw [← integral_sub haInt hbInt]
  have he := ae_of_all μ (fun z =>
    originalKernel_residue_slow_quadrature_varying L q hL hq hqL hsmall
      (F z) (hLip z) (hbound z))
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem affineKernel_residue_slow_retained_quadrature
    {G R Z : Type*} [Fintype G] [DecidableEq G] [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (H : G → ℕ) (q : ℕ) [NeZero q] (hH : ∀ g, 0 < H g)
    (hq : 0 < q) (hqH : ∀ g, q ≤ H g)
    (hsmall : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H g) <
      volume.real (scalarCubeDomain Empty))
    (lower : G → ℝ) (step S : ℝ) (hS : 0 < S) (hstep : 0 ≤ step)
    (hspan : ∀ g, step * ((H g - 1 : ℕ) : ℝ) ≤ S)
    (residueMap : (G → ZMod q) → R) (F : Z → R → (G → ℝ) → ℂ)
    (hMeas : ∀ r, Measurable (fun zx : Z × (G → ℝ) => F zx.1 r zx.2))
    {K : ℝ≥0} (hLip : ∀ z r, LipschitzWith K (F z r))
    (hbound : ∀ z r x, ‖F z r x‖ ≤ 1) :
    ‖(∫ z, (FiniteProbabilityWeights.pi
        (fun g => integerScalarCubeWeights Empty (H g) (hH g))).complexMean
          (fun y => F z (residueMap (fun g => ((y g none : ℤ) : ZMod q)))
            (fun g => (lower g + step * (y g none : ℝ)) / S)) ∂μ) -
      ∫ z, 𝔼 r : G → ZMod q, ∫ x,
        F z (residueMap r) (affineKernelContinuousPoint lower step S H x)
          ∂scalarCubeProductMeasure G Empty ∂μ‖ ≤
      (1 + 2 * (2 * scalarCubeGridBoundaryConstant Empty /
        volume.real (scalarCubeDomain Empty) + K) + K) * ∑ g, (q : ℝ) / H g := by
  let p := FiniteProbabilityWeights.pi
    (fun g => integerScalarCubeWeights Empty (H g) (hH g))
  let a (z : Z) := p.complexMean
    (fun y => F z (residueMap (fun g => ((y g none : ℤ) : ZMod q)))
      (fun g => (lower g + step * (y g none : ℝ)) / S))
  let b (z : Z) := 𝔼 r : G → ZMod q,
    ∫ x, F z (residueMap r) (affineKernelContinuousPoint lower step S H x)
      ∂scalarCubeProductMeasure G Empty
  have haMeas : Measurable a := by
    unfold a FiniteProbabilityWeights.complexMean
    apply Finset.measurable_sum
    intro y _
    exact measurable_const.mul ((hMeas _).comp (measurable_id.prodMk measurable_const))
  have haBound (z : Z) : ‖a z‖ ≤ 1 := by
    apply (p.norm_complexMean_le_mean_norm _).trans
    exact (p.mean_mono (fun y => hbound z _ _)).trans_eq (p.mean_const 1)
  have haInt : Integrable a μ :=
    (integrable_const (1 : ℝ)).mono' haMeas.aestronglyMeasurable (ae_of_all μ haBound)
  have hAffine : Measurable (affineKernelContinuousPoint lower step S H) :=
    (affineKernelContinuousPoint_lipschitz lower step S H hS hstep hspan).continuous.measurable
  have hiMeas (r : G → ZMod q) :
      StronglyMeasurable (fun z => ∫ x,
        F z (residueMap r) (affineKernelContinuousPoint lower step S H x)
          ∂scalarCubeProductMeasure G Empty) := by
    have hm : Measurable (fun zx : Z × (G → Option Empty → ℝ) =>
        F zx.1 (residueMap r) (affineKernelContinuousPoint lower step S H zx.2)) :=
      (hMeas _).comp (measurable_fst.prodMk (hAffine.comp measurable_snd))
    exact hm.stronglyMeasurable.integral_prod_right'
  have hiBound (z : Z) (r : G → ZMod q) :
      ‖∫ x, F z (residueMap r) (affineKernelContinuousPoint lower step S H x)
        ∂scalarCubeProductMeasure G Empty‖ ≤ 1 := by
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
      (ae_of_all (scalarCubeProductMeasure G Empty) (fun x => hbound z _ _))
  have hbMeas : Measurable b := by
    unfold b
    simp only [Fintype.expect_eq_sum_div_card]
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun r _ => (hiMeas r).measurable)
  have hbBound (z : Z) : ‖b z‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    exact (Finset.expect_le_expect (fun r _ => hiBound z r)).trans_eq (by simp)
  have hbInt : Integrable b μ :=
    (integrable_const (1 : ℝ)).mono' hbMeas.aestronglyMeasurable (ae_of_all μ hbBound)
  change ‖(∫ z, a z ∂μ) - ∫ z, b z ∂μ‖ ≤ _
  rw [← integral_sub haInt hbInt]
  have he := ae_of_all μ (fun z =>
    affineKernel_residue_slow_quadrature H q hH hq hqH hsmall lower step S hS hstep hspan
      residueMap (F z) (hLip z) (hbound z))
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const he

end Erdos3

end

end OAI
