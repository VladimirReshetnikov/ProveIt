import OAI.Combinatorics.Progressions.Probability.PositiveDensityNormalization

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory

theorem joint_normalization_integral_compare {X Y C : Type*} [Fintype X] [Fintype Y]
    [MeasurableSpace C] (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (μ : Measure C) [IsProbabilityMeasure μ]
    (D : C → X × Y → ℝ) (hDm : ∀ z, Measurable (fun c => D c z))
    (hD0 : ∀ c z, 0 ≤ D c z)
    (hlocal : ∀ c x, 0 < q.mean (fun y => D c (x,y)))
    (hglobal : ∀ c, 0 < (p.prod q).mean (D c))
    (f : X × Y → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) {ε : ℝ}
    (hclose : ∀ c x, |q.mean (fun y => D c (x,y))-1| ≤ ε) :
    ‖(∫ c, (p.prod q).normalizedDensityTest (D c) f ∂μ) -
      p.complexMean (fun x => ∫ c, q.normalizedDensityTest
        (fun y => D c (x,y)) (fun y => f (x,y)) ∂μ)‖ ≤ 2*ε := by
  have hj := (p.prod q).normalizedDensityTest_integrable μ D hDm hD0 hglobal f hf
  have hl (x : X) := q.normalizedDensityTest_integrable μ (fun c y => D c (x,y))
    (fun y => hDm (x,y)) (fun c y => hD0 c (x,y)) (fun c => hlocal c x)
    (fun y => f (x,y)) (fun y => hf (x,y))
  have hli := p.complexMean_integrable μ
    (fun c x => q.normalizedDensityTest (fun y => D c (x,y)) (fun y => f (x,y))) hl
  rw [← p.integral_complexMean μ _ hl, ← integral_sub hj hli]
  have h := norm_integral_le_of_norm_le (integrable_const (2*ε) (μ := μ))
    (ae_of_all μ (fun c => p.joint_normalization_compare q (D c) (hD0 c)
      (hlocal c) (hglobal c) f hf (hclose c)))
  simpa only [integral_const, probReal_univ, one_smul] using h

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {B K I : Type*} [Fintype K] [Fintype I]
variable (A : Finset B) (hA : A.Nonempty)
variable (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)

theorem selectedJointFiniteLaw_local_real_comparison (D : B → (K × I → ℤ) → ℝ)
    (hD0 : ∀ a z, 0 ≤ D a z) (hD : 0 < selectedJointDensityMass A modulus T W D)
    (hlocal : ∀ a, 0 < selectedResidueDensityMass modulus T W (D a))
    (f : B → (K × I → ℤ) → ℝ) (hf : ∀ a z, |f a z| ≤ 1) {ε : ℝ}
    (hclose : ∀ a, |selectedResidueDensityMass modulus T W (D a)-1| ≤ ε) :
    |(selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).mean
        (fun z => f z.1.val z.2.val) -
      (𝔼 a ∈ A, ∑' z, (selectedResidueDensityPMF modulus T W hW hZ (D a) (hD0 a) (hlocal a) z).toReal *
        f a z)| ≤ 2*ε := by
  have h := selectedJointFiniteLaw_local_comparison A hA modulus T W hW hZ D hD0 hD hlocal
    (fun a z => (f a z : ℂ)) (fun a z => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf a z) hclose
  simp only [FiniteProbabilityWeights.complexMean_ofReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_tsum] at h
  have he (g : B → ℝ) : (𝔼 a ∈ A, (g a : ℂ)) = ((Finset.expect A g : ℝ) : ℂ) := by
    simp only [Finset.expect_eq_sum_div_card, Complex.ofReal_div,
      Complex.ofReal_sum, Complex.ofReal_natCast]
  rw [he (fun a => ∑' z,
    (selectedResidueDensityPMF modulus T W hW hZ (D a) (hD0 a) (hlocal a) z).toReal * f a z)] at h
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

theorem selectedJointFiniteLaw_integral_local_comparison {C : Type*} [MeasurableSpace C]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (D : C → B → (K × I → ℤ) → ℝ) (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass A modulus T W (D c))
    (hlocal : ∀ c a, 0 < selectedResidueDensityMass modulus T W (D c a))
    (f : B → (K × I → ℤ) → ℂ) (hf : ∀ a z, ‖f a z‖ ≤ 1) {ε : ℝ}
    (hclose : ∀ c a, |selectedResidueDensityMass modulus T W (D c a)-1| ≤ ε) :
    ‖(∫ c, (selectedJointFiniteLaw A hA modulus T W hW hZ (D c) (hD0 c) (hD c)).complexMean
        (fun z => f z.1.val z.2.val) ∂μ) -
      (𝔼 a ∈ A, ∫ c, ∑' z,
        ((selectedResidueDensityPMF modulus T W hW hZ (D c a) (hD0 c a) (hlocal c a) z).toReal : ℂ) *
          f a z ∂μ)‖ ≤ 2*ε := by
  let p := FiniteProbabilityWeights.uniformFinset A hA
  let q := selectedResidueFiniteLaw modulus T W hW hZ
  have h := p.joint_normalization_integral_compare q μ (fun c z => D c z.1.val z.2.val)
    (fun z => hDm z.1.val z.2.val) (fun c z => hD0 c z.1.val z.2.val)
    (fun c a => by
      change 0 < q.mean (fun y => D c a.val y.val)
      rw [selectedResidueFiniteLaw_densityMass modulus T W hW hZ (D c a.val)]
      exact hlocal c a.val)
    (fun c => by change 0 < (selectedJointReference A hA modulus T W hW hZ).mean _
                 rw [selectedJointReference_densityMass]; exact hD c)
    (fun z => f z.1.val z.2.val) (fun z => hf z.1.val z.2.val)
    (fun c a => by
      change |q.mean (fun y => D c a.val y.val)-1| ≤ ε
      rw [selectedResidueFiniteLaw_densityMass modulus T W hW hZ (D c a.val)]
      exact hclose c a.val)
  have he (c : C) (a : B) := selectedResidueDensityPMF_normalizedDensityTest modulus T W hW hZ
    (D c a) (hD0 c a) (hlocal c a) (f a)
  have hm := FiniteProbabilityWeights.uniformFinset_complexMean A hA
    (fun a => ∫ c, q.normalizedDensityTest (fun z => D c a z.val) (fun z => f a z.val) ∂μ)
  dsimp only [p] at h
  rw [hm] at h
  simpa only [selectedJointFiniteLaw_complexMean, he, selectedJointReference, q] using h

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory
open scoped BigOperators Classical

theorem fixedScaleJointMarginalTransfer
    {K I C : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    [MeasurableSpace C] (μ : Measure C) [IsProbabilityMeasure μ]
    (root : K → ℤ) (N margin : I → ℕ) (hmargin : ∀ i, 2 * margin i < N i)
    (stride : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I stride))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z)
    (hfit : ∀ i, physicalSiteWidth root W i ≤ (margin i : ℝ))
    (D : C → (I → ℤ) → (Option K × I → ℤ) → ℝ)
    (hDm : ∀ a z, Measurable (fun c => D c a z))
    (hD0 : ∀ c a z, 0 ≤ D c a z)
    (hD : ∀ c, 0 < selectedJointDensityMass (trimmedIntegerBox N margin) stride T W (D c))
    (hlocal : ∀ c a, 0 < selectedResidueDensityMass stride T W (D c a))
    {ε η : ℝ}
    (hclose : ∀ c a, |selectedResidueDensityMass stride T W (D c a) - 1| ≤ ε)
    (hmix : ∀ a (ψ : (I → ℝ) → ℂ), (∀ v, ‖ψ v‖ ≤ 1) →
      ‖(∫ c, ∑' z, ((selectedResidueDensityPMF stride T W hW hZ (D c a)
          (hD0 c a) (hlocal c a) z).toReal : ℂ) * ψ (physicalAffineSite root z) ∂μ) -
        ∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
          ψ (physicalAffineSite root z)‖ ≤ η) :
    ∀ φ : (I → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
      let f := fun c =>
        (selectedJointFiniteLaw (trimmedIntegerBox N margin)
          (trimmedIntegerBox_nonempty N margin hmargin) stride T W hW hZ
          (D c) (hD0 c) (hD c)).complexMean
            (fun z => φ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite root z.2.val))
      Integrable f μ ∧
        ‖(∫ c, f c ∂μ) - (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
          2 * ε + η + 2 * ∑ i, 2 * (margin i : ℝ) / N i := by
  intro φ hφ
  let Q := trimmedIntegerBox N margin
  have hQ : Q.Nonempty := trimmedIntegerBox_nonempty N margin hmargin
  constructor
  · have hi := (selectedJointReference Q hQ stride T W hW hZ).normalizedDensityTest_integrable μ
      (fun c z => D c z.1.val z.2.val)
      (fun z => hDm z.1.val z.2.val) (fun c z => hD0 c z.1.val z.2.val)
      (fun c => by
        rw [selectedJointReference_densityMass Q hQ stride T W hW hZ (D c)]
        exact hD c)
      (fun z => φ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite root z.2.val))
      (fun z => hφ _)
    apply hi.congr
    filter_upwards [] with c
    exact (selectedJointFiniteLaw_complexMean Q hQ stride T W hW hZ
      (D c) (hD0 c) (hD c)
      (fun a z => φ ((fun i => (a i : ℝ)) + physicalAffineSite root z))).symm
  · have hjoint := selectedJointFiniteLaw_integral_local_comparison Q hQ stride T W hW hZ μ
      D hDm hD0 hD hlocal
      (fun a z => φ ((fun i => (a i : ℝ)) + physicalAffineSite root z))
      (fun _ _ => hφ _) hclose
    have hreference :
        ‖(𝔼 a ∈ Q, ∫ c, ∑' z,
          ((selectedResidueDensityPMF stride T W hW hZ (D c a)
            (hD0 c a) (hlocal c a) z).toReal : ℂ) *
            φ ((fun i => (a i : ℝ)) + physicalAffineSite root z) ∂μ) -
          (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
          η + 2 * ∑ i, 2 * (margin i : ℝ) / N i := by
      refine selectedResidue_trimmed_comparison_transfer root N margin hmargin stride T W hW hZ
        hfit (fun x => φ (fun i => (x i : ℝ))) (fun _ _ => hφ _) _ ?_
      intro a _
      have h := hmix a (fun v => φ ((fun i => (a i : ℝ)) + v)) (fun _ => hφ _)
      have hcast (z : Option K × I → ℤ) :
          (fun i => ((a + integerPhysicalSite root z) i : ℝ)) =
            (fun i => (a i : ℝ)) + physicalAffineSite root z := by
        funext i
        simp only [Pi.add_apply, Int.cast_add, integerPhysicalSite_cast_apply]
      simpa only [hcast] using h
    exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      (add_le_add hjoint hreference)).trans_eq (by ring)

end Erdos3.BooleanCubeKernel

end

end OAI
