import OAI.Combinatorics.Progressions.Geometry.CanonicalSpatialSupport

namespace OAI

section

namespace Erdos3

open scoped NNReal BigOperators

variable {D : Type*} [Fintype D] {I : D → Type*} [∀ d, Fintype (I d)]

theorem sigmaAxisWeight_output_bounds (f : ∀ d, (I d → ℝ) → ℝ)
    {B K : ℝ≥0} (hB : 1 ≤ B)
    (hf : ∀ d, LipschitzWith K (f d)) (hb : ∀ d x, |f d x| ≤ B) :
    (∀ x, |sigmaAxisWeight f x| ≤ (B : ℝ) ^ Fintype.card D) ∧
      LipschitzWith (Fintype.card D * K * B ^ Fintype.card D) (sigmaAxisWeight f) := by
  have hp (d : D) : LipschitzWith 1 (sigmaAxisProjection I d) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub] using
      sigmaAxisProjection_norm_apply_le I d (x - y)
  have hcomp (d : D) : LipschitzWith K (fun x => f d (sigmaAxisProjection I d x)) := by
    simpa only [mul_one, Function.comp_def] using (hf d).comp (hp d)
  exact bounded_lipschitz_real_prod (fun d x => f d (sigmaAxisProjection I d x))
    hB hcomp (fun d x => hb d (sigmaAxisProjection I d x))

theorem sigmaAxisWeight_zero_outside (f : ∀ d, (I d → ℝ) → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hf : ∀ d x, R < ‖x‖ → f d x = 0)
    (x : (Σ d, I d) → ℝ) (hx : R < ‖x‖) : sigmaAxisWeight f x = 0 := by
  classical
  have hlarge : ∃ d, R < ‖sigmaAxisProjection I d x‖ := by
    by_contra hn
    have hnorm : ‖x‖ ≤ R := by
      apply (pi_norm_le_iff_of_nonneg hR).2
      intro i
      exact (norm_le_pi_norm (sigmaAxisProjection I i.1 x) i.2).trans
        (le_of_not_gt (fun hi => hn ⟨i.1, hi⟩))
    exact (not_lt_of_ge hnorm) hx
  obtain ⟨d, hd⟩ := hlarge
  change (∏ a, f a (sigmaAxisProjection I a x)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ d) (hf d _ hd)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory BooleanCubeKernel
open scoped Matrix NNReal BigOperators

variable {I J X : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype X]
variable (s : I ↪ J) (root : J → ℤ) (D : Matrix I J ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

noncomputable def canonicalSpatialKernelMap
    (p : (UnselectedColumn s → ℝ) × ((Unit ⊕ I) → ℝ)) : (Unit ⊕ I) → ℝ :=
  normalizedIntegerPivot (selectedSpatialPivot root D s)
      (anisotropicSpatialScale I (1 + W) 1) (physicalSpatialOutputScale I (1 + W) 1 L) *ᵥ p.2 +
    normalizedIntegerColumns (selectedSpatialFreeColumns root D s) (fun _ => 1)
      (physicalSpatialOutputScale I (1 + W) 1 L) *ᵥ p.1

theorem canonicalSpatialKernelDensity_probability_data :
    (∀ y, 0 ≤ canonicalSpatialKernelDensity s root D hp W L hW hL y) ∧
      Integrable (canonicalSpatialKernelDensity s root D hp W L hW hL) ∧
      (∫ y, canonicalSpatialKernelDensity s root D hp W L hW hL y) = 1 := by
  have hf : Integrable (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)) :=
    Integrable.of_integral_ne_zero ((smoothSplitProfile_integral _ _).trans_ne one_ne_zero)
  refine ⟨pivotOutputDensity_nonneg _ _ (fun p => (smoothSplitProfile_range _ _ p).1),
    pivotOutputDensity_integrable _ _ hf, ?_⟩
  exact (pivotOutputDensity_integral _ _ hf).trans (smoothSplitProfile_integral _ _)

theorem canonicalSpatialKernelDensity_image_law :
    Measure.map (canonicalSpatialKernelMap s root D (W := W) (L := L))
      (realDensityMeasure volume (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I))) =
      realDensityMeasure volume (canonicalSpatialKernelDensity s root D hp W L hW hL) := by
  exact normalizedFiberDensity_law _ hp _ _ _ _ _ _
    (Integrable.of_integral_ne_zero ((smoothSplitProfile_integral _ _).trans_ne one_ne_zero))
    (fun p => (smoothSplitProfile_range _ _ p).1)

variable [IsEmpty I]

theorem canonicalSpatialSiteDensity_eq_kernel :
    canonicalSpatialSiteDensity s root D hp W L hW hL =
      canonicalSpatialKernelDensity s root D hp W L hW hL := by
  funext y
  unfold canonicalSpatialSiteDensity coordinateRescaledDensity
  congr 1
  funext i
  cases i with
  | inl u =>
    change (1 + W) / (1 + W) * y (Sum.inl u) = y (Sum.inl u)
    rw [div_self (by linarith : (1 + W : ℝ) ≠ 0), one_mul]
  | inr i => exact isEmptyElim i

noncomputable def canonicalZeroSpatialJointDensity : ((Σ _ : X, Unit ⊕ I) → ℝ) → ℝ :=
  sigmaAxisWeight (fun _ : X => canonicalSpatialSiteDensity s root D hp W L hW hL)

theorem canonicalZeroSpatialJointDensity_probability_data :
    (∀ y, 0 ≤ canonicalZeroSpatialJointDensity (X := X) s root D hp hW hL y) ∧
      Integrable (canonicalZeroSpatialJointDensity (X := X) s root D hp hW hL) ∧
      (∫ y, canonicalZeroSpatialJointDensity (X := X) s root D hp hW hL y) = 1 := by
  have hd := canonicalSpatialKernelDensity_probability_data s root D hp hW hL
  have he := canonicalSpatialSiteDensity_eq_kernel s root D hp hW hL
  have hm : (∫ y, canonicalZeroSpatialJointDensity (X := X) s root D hp hW hL y) = 1 := by
    unfold canonicalZeroSpatialJointDensity
    rw [sigmaAxisWeight_integral]
    simp only [he, hd.2.2, Finset.prod_const_one]
  exact ⟨sigmaAxisWeight_nonneg _ (fun _ y => by rw [he]; exact hd.1 y),
    Integrable.of_integral_ne_zero (hm.trans_ne one_ne_zero), hm⟩

theorem canonicalZeroSpatialJointDensity_image_law :
    sigmaAxisMeasure (fun _ : X => Measure.map
      (canonicalSpatialKernelMap s root D (W := W) (L := L))
      (realDensityMeasure volume (smoothSplitProfile (UnselectedColumn s) (Unit ⊕ I)))) =
        realDensityMeasure volume
          (canonicalZeroSpatialJointDensity (X := X) s root D hp hW hL) := by
  have hd := canonicalSpatialKernelDensity_probability_data s root D hp hW hL
  simp_rw [canonicalSpatialKernelDensity_image_law s root D hp hW hL]
  rw [sigmaAxisMeasure_density _ (fun _ => hd.2.1) (fun _ => hd.1)]
  simp only [canonicalZeroSpatialJointDensity, canonicalSpatialSiteDensity_eq_kernel]

theorem canonicalZeroSpatialJointDensity_bounds
    {κ : ℝ} (hκ : 0 < κ) (hr : ∀ j, |(root j : ℝ)| ≤ 1 + W)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    let C := Real.toNNReal (anisotropicSpatialDensityCap s κ) + 1
    let K := Real.toNNReal (anisotropicSpatialDensityLip s κ)
    (∀ y, canonicalZeroSpatialJointDensity (X := X) s root D hp hW hL y ∈
      Set.Icc (0 : ℝ) (C ^ Fintype.card X)) ∧
      LipschitzWith (Fintype.card X * K * C ^ Fintype.card X)
        (canonicalZeroSpatialJointDensity (X := X) s root D hp hW hL) := by
  intro C K
  have hb := anisotropicSpatialKernelDensity_bounds root D s
    (by linarith : (0 : ℝ) < 1 + W) zero_lt_one hL hκ
    (fun j => by simpa only [mul_one] using hr j) (fun i => isEmptyElim i) hminor
  have hc : ∀ y, |canonicalSpatialSiteDensity s root D hp W L hW hL y| ≤ C := by
    intro y
    rw [canonicalSpatialSiteDensity_eq_kernel]
    exact (hb.1 y).trans (by
      change anisotropicSpatialDensityCap s κ ≤ (Real.toNNReal _ : ℝ) + 1
      rw [Real.coe_toNNReal _ (anisotropicSpatialDensityCap_nonneg s hκ.le)]
      linarith)
  have hl : LipschitzWith K (canonicalSpatialSiteDensity s root D hp W L hW hL) := by
    rw [canonicalSpatialSiteDensity_eq_kernel]
    exact hb.2
  have ht := sigmaAxisWeight_output_bounds (fun _ : X =>
    canonicalSpatialSiteDensity s root D hp W L hW hL)
    (by simp [C] : 1 ≤ C) (fun _ => hl) (fun _ => hc)
  refine ⟨fun y => ⟨(canonicalZeroSpatialJointDensity_probability_data s root D hp hW hL).1 y,
    ?_⟩, ht.2⟩
  exact (le_abs_self _).trans (by simpa only [canonicalZeroSpatialJointDensity, NNReal.coe_pow] using ht.1 y)

theorem canonicalZeroSpatialJointDensity_zero_outside
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (v : (Σ _ : X, Unit ⊕ I) → ℝ) (hv : 3 < ‖v‖) :
    canonicalZeroSpatialJointDensity s root D hp hW hL v = 0 := by
  apply sigmaAxisWeight_zero_outside _ (by norm_num : (0 : ℝ) ≤ 3) ?_ v hv
  intro x y hy
  apply canonicalSpatialSiteDensity_zero_outside s root D hp hW hL hroot
    (fun i => isEmptyElim i) y
  by_contra hn
  have hbound : ‖y‖ ≤ 3 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)).mpr
    intro i
    cases i with
    | inl u =>
      cases u
      simpa [Real.norm_eq_abs, spatialStar] using
        (le_of_not_gt (fun h => hn ⟨Sum.inl (), h⟩))
    | inr i => exact isEmptyElim i
  exact (not_lt_of_ge hbound) hy

end Erdos3

end

end OAI
