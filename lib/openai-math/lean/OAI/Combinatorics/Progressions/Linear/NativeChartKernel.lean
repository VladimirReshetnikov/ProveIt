/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget

namespace OAI

section

namespace Erdos3

open Set
open scoped NNReal

variable {ι X : Type*} [Fintype ι] [MetricSpace X]

noncomputable def chartCoordinateKernel (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) : (ι → ℝ) → ℝ := chartCutoff phi.symm F

omit [Fintype ι] in
theorem chartCoordinateKernel_of_mem (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) {v : ι → ℝ} (hv : v ∈ phi.source) :
    chartCoordinateKernel phi F v = F (phi v) := by
  classical
  change (if v ∈ phi.source then F (phi v) else 0) = _
  rw [ite_eq_left hv]

omit [Fintype ι] in
theorem chartCoordinateKernel_of_not_mem (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) {v : ι → ℝ} (hv : v ∉ phi.source) :
    chartCoordinateKernel phi F v = 0 := by
  classical
  change (if v ∈ phi.source then F (phi v) else 0) = _
  rw [ite_eq_right hv]

omit [Fintype ι] in
theorem chartCoordinateKernel_recover (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) {x : X} (hx : x ∈ phi.target) :
    chartCoordinateKernel phi F (phi.symm x) = F x :=
  chartCutoff_apply phi.symm F hx

omit [Fintype ι] in
theorem chartCoordinateKernel_range (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (v : ι → ℝ) :
    0 ≤ chartCoordinateKernel phi F v ∧ chartCoordinateKernel phi F v ≤ 1 :=
  chartCutoff_range phi.symm F hF v

theorem chartCoordinateKernel_support (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) {r : ℝ} (hr : 0 < r)
    (hsource : phi.source = {v | ∀ i, |v i| < r})
    (hinner : tsupport F ⊆ phi '' Metric.closedBall 0 (3 * r / 4)) :
    Function.support (chartCoordinateKernel phi F) ⊆ Metric.closedBall 0 (3 * r / 4) := by
  intro v hv
  change chartCoordinateKernel phi F v ≠ 0 at hv
  have hvs : v ∈ phi.source := by
    by_contra h
    exact hv (chartCoordinateKernel_of_not_mem phi F h)
  have hFv : F (phi v) ≠ 0 := by
    rwa [chartCoordinateKernel_of_mem phi F hvs] at hv
  obtain ⟨u, hu, heq⟩ := hinner (subset_closure hFv)
  have hus := closedBox_subset_chart_source phi hr hsource hu
  have huv : u = v := by
    calc
      u = phi.symm (phi u) := (phi.left_inv hus).symm
      _ = phi.symm (phi v) := congrArg phi.symm heq
      _ = v := phi.left_inv hvs
  exact huv ▸ hu

theorem chartCoordinateKernel_lipschitz (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) (A K r : ℝ≥0) (hr : 0 < r)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hLip : LipschitzWith A F)
    (hsource : phi.source = {v | ∀ i, |v i| < (r : ℝ)})
    (hinner : tsupport F ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4))
    (hForward : LipschitzOnWith K phi phi.source) :
    LipschitzWith (A * K + 1 / (r / 4)) (chartCoordinateKernel phi F) := by
  apply lipschitz_chartCutoff phi.symm F A K (r / 4) (by positivity) hF hLip hForward
  intro v hv hFv y hy
  change v ∈ phi.source at hv
  change y ∉ phi.source at hy
  have hvk : chartCoordinateKernel phi F v ≠ 0 := by
    rwa [chartCoordinateKernel_of_mem phi F hv]
  have hball := chartCoordinateKernel_support phi F hr hsource hinner hvk
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  obtain ⟨i, hyi⟩ : ∃ i, (r : ℝ) ≤ |y i| := by
    simpa only [hsource, mem_ofPred_eq, not_forall, not_lt] using hy
  have hvi : |v i| ≤ 3 * (r : ℝ) / 4 := by
    calc
      |v i| = ‖v i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖v‖ := norm_le_pi_norm v i
      _ ≤ _ := hball
  have hd : |y i - v i| ≤ dist v y := by
    simpa only [Real.dist_eq, abs_sub_comm] using dist_le_pi_dist v y i
  have ht : |y i| ≤ |y i - v i| + |v i| := by
    simpa only [sub_add_cancel] using abs_add_le (y i - v i) (v i)
  change (r : ℝ) / 4 ≤ dist v y
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem chartKernelScaling_lipschitz (d B : ℕ) :
    LipschitzWith (B : ℝ≥0) (fun x : Fin d → ℝ => (B : ℝ) • x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) B), NNReal.coe_natCast]
  exact le_rfl

variable {X : Type*} [MetricSpace X] {d : ℕ}
  (phi : OpenPartialHomeomorph (Fin d → ℝ) X) (F : X → ℝ)
  (A K r : ℝ≥0) (hr : 0 < r) (hr1 : r ≤ 1)
  (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hLip : LipschitzWith A F)
  (hsource : phi.source = {v | ∀ i, |v i| < (r : ℝ)})
  (hinner : tsupport F ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4))
  (hForward : LipschitzOnWith K phi phi.source) (B : ℕ) (hB : 4 ≤ B)

noncomputable def scaledChartKernel : PatchKernel d where
  value x := chartCoordinateKernel phi F ((B : ℝ) • x)
  nonneg x := (chartCoordinateKernel_range phi F hF _).1
  le_one x := (chartCoordinateKernel_range phi F hF _).2
  support x hx i := by
    have hb := chartCoordinateKernel_support phi F hr hsource hinner hx
    rw [Metric.mem_closedBall, dist_zero_right] at hb
    have hi : (B : ℝ) * |x i| ≤ 3 * (r : ℝ) / 4 := by
      calc
        (B : ℝ) * |x i| = ‖((B : ℝ) • x) i‖ := by
          simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (Nat.cast_nonneg (α := ℝ) B)]
        _ ≤ ‖(B : ℝ) • x‖ := norm_le_pi_norm ((B : ℝ) • x) i
        _ ≤ _ := hb
    have hBr : (4 : ℝ) ≤ B := by exact_mod_cast hB
    have hsmall := mul_le_mul_of_nonneg_right hBr (abs_nonneg (x i))
    have hr1' : (r : ℝ) ≤ 1 := hr1
    linarith
  lip := (A * K + 1 / (r / 4)) * B
  lipschitz := by
    simpa only [Function.comp_def] using
      (chartCoordinateKernel_lipschitz phi F A K r hr hF hLip hsource hinner hForward).comp
        (chartKernelScaling_lipschitz d B)

theorem scaledChartKernel_value (x : Fin d → ℝ) :
    (scaledChartKernel phi F A K r hr hr1 hF hLip hsource hinner hForward B hB).value x =
      chartCoordinateKernel phi F ((B : ℝ) • x) := rfl

theorem scaledChartKernel_lip :
    (scaledChartKernel phi F A K r hr hr1 hF hLip hsource hinner hForward B hB).lip =
      (A * K + 1 / (r / 4)) * B := rfl

theorem scaledChartKernel_recover {x : X} (hx : x ∈ phi.target) :
    (scaledChartKernel phi F A K r hr hr1 hF hLip hsource hinner hForward B hB).value
      (fun i => phi.symm x i / B) = F x := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  have he : (B : ℝ) • (fun i => phi.symm x i / B) = phi.symm x := by
    funext i
    change (B : ℝ) * (phi.symm x i / B) = phi.symm x i
    field_simp [hB0]
  rw [scaledChartKernel_value, he]
  exact chartCoordinateKernel_recover phi F hx

theorem chartKernel_log_bound {A K r : ℝ≥0} {B : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (hA : (A : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p)
    (hr : 1 / (r : ℝ) ≤ Real.exp p) (hB : (B : ℝ) ≤ Real.exp p) :
    Real.log (2 + (((A * K + 1 / (r / 4)) * B : ℝ≥0) : ℝ)) ≤ 3 * p + 6 := by
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_div,
    NNReal.coe_natCast, NNReal.coe_one, NNReal.coe_ofNat]
  rw [show 1 / ((r : ℝ) / 4) = 4 * (1 / (r : ℝ)) by ring]
  have he : 1 ≤ Real.exp p := Real.one_le_exp hp
  have he3 : 1 ≤ Real.exp p ^ 3 := one_le_pow₀ he
  have he23 : Real.exp p ^ 2 ≤ Real.exp p ^ 3 := pow_le_pow_right₀ he (by decide)
  have hAK := mul_le_mul hA hK K.coe_nonneg (Real.exp_nonneg p)
  have hfour := mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 4)
  have hprod := mul_le_mul (add_le_add hAK hfour) hB (Nat.cast_nonneg B)
    (show 0 ≤ Real.exp p * Real.exp p + 4 * Real.exp p by positivity)
  have hseven : (7 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
  have hlast := mul_le_mul_of_nonneg_left hseven (show 0 ≤ Real.exp p ^ 3 by positivity)
  rw [Real.exp_add]
  have heq : Real.exp (3 * p) = Real.exp p ^ 3 := by
    simpa using Real.exp_nat_mul p 3
  rw [heq]
  nlinarith

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} (T : D.Niltest w)

theorem realObservable_lipschitz :
    letI := D.metricSpace
    LipschitzWith T.lipBound (fun x => (T.observable x).re) := by
  let := D.metricSpace
  simpa only [one_mul, Function.comp_def, RCLike.re_eq_complex_re] using
    (RCLike.lipschitzWith_re (K := ℂ)).comp T.lipschitz

theorem realObservable_tsupport :
    tsupport (fun x => (T.observable x).re) ⊆ tsupport T.observable := by
  apply closure_mono
  intro x hx
  change T.observable x ≠ 0
  intro hzero
  apply hx
  change (T.observable x).re = 0
  rw [hzero, Complex.zero_re]

variable (hT : T.UnitIntervalValued) (phi : OpenPartialHomeomorph (Fin d → ℝ) D.Space)
  (K r : ℝ≥0) (hr : 0 < r) (hr1 : r ≤ 1)
  (hsource : phi.source = {v | ∀ i, |v i| < (r : ℝ)})
  (hinner : tsupport T.observable ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4))
  (hForward : letI := D.metricSpace; LipschitzOnWith K phi phi.source) (hgrid : 4 ≤ D.grid)

noncomputable def chartKernel : PatchKernel d := by
  let := D.metricSpace
  exact scaledChartKernel phi (fun x => (T.observable x).re) T.lipBound K r hr hr1
    (fun x => (hT x).2) T.realObservable_lipschitz hsource
    (T.realObservable_tsupport.trans hinner) hForward D.grid hgrid

theorem chartKernel_lip :
    (T.chartKernel hT phi K r hr hr1 hsource hinner hForward hgrid).lip =
      (T.lipBound * K + 1 / (r / 4)) * D.grid := rfl

theorem chartKernel_value (v : Fin d → ℝ) :
    letI := D.metricSpace
    (T.chartKernel hT phi K r hr hr1 hsource hinner hForward hgrid).value v =
      chartCoordinateKernel phi (fun x => (T.observable x).re) ((D.grid : ℝ) • v) := rfl

theorem chartKernel_recover {x : D.Space} (hx : x ∈ phi.target) :
    (T.chartKernel hT phi K r hr hr1 hsource hinner hForward hgrid).value
      (fun i => phi.symm x i / D.grid) = (T.observable x).re := by
  let := D.metricSpace
  exact scaledChartKernel_recover phi (fun x => (T.observable x).re) T.lipBound K r hr hr1
    (fun x => (hT x).2) T.realObservable_lipschitz hsource
    (T.realObservable_tsupport.trans hinner) hForward D.grid hgrid hx

theorem chartKernel_log_bound {p : ℝ} (hp : 0 ≤ p) (hcomplexity : T.ComplexityLE p)
    (hK : (K : ℝ) ≤ Real.exp p) (hri : 1 / (r : ℝ) ≤ Real.exp p) :
    Real.log (2 + ((T.chartKernel hT phi K r hr hr1 hsource hinner hForward hgrid).lip : ℝ)) ≤
      3 * p + 6 := by
  rw [T.chartKernel_lip]
  apply Erdos3.chartKernel_log_bound hp ?_ hK hri hcomplexity.1.2.1
  have hb := observable_budget hcomplexity
  linarith [T.normBound.coe_nonneg]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
