import OAI.Combinatorics.Progressions.Estimates.RiemannianLipschitz
import OAI.Combinatorics.Progressions.Estimates.TangentModelVector

namespace OAI

section

namespace Erdos3

open Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Bundle Topology

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)]

theorem coordinate_edist_le_mul_pathELength {f : M → F} {C : ℝ≥0}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ)
    {a b : ℝ} (hab : a ≤ b)
    (hbound : ∀ t ∈ Icc a b, ∀ v : TangentSpace I (γ t),
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f (γ t) v)‖ₑ ≤ C * ‖v‖ₑ) :
    edist (f (γ a)) (f (γ b)) ≤ C * pathELength I γ a b := by
  have hsmooth : ContDiff ℝ 1 (f ∘ γ) := (hf.comp hγ).contDiff
  calc
    _ = ‖(f ∘ γ) b - (f ∘ γ) a‖ₑ := by rw [edist_comm, edist_eq_enorm_sub]; rfl
    _ ≤ ∫⁻ t in Icc a b, ‖deriv (f ∘ γ) t‖ₑ :=
      enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hsmooth.contDiffOn hab
    _ ≤ ∫⁻ t in Icc a b, C * ‖mfderiv 𝓘(ℝ) I γ t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hchain := mfderiv_comp_apply t (hf.mdifferentiableAt one_ne_zero)
        (hγ.mdifferentiableAt one_ne_zero) 1
      rw [mfderiv_eq_fderiv] at hchain
      change deriv (f ∘ γ) t = tangentModelVector
        (mfderiv I 𝓘(ℝ, F) f (γ t) (mfderiv 𝓘(ℝ) I γ t 1)) at hchain
      rw [hchain]
      exact hbound t ht _
    _ = C * pathELength I γ a b := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, pathELength_eq_lintegral_mfderiv_Icc]

theorem coordinate_path_stays_in_closedBall {f : M → F} {C r : ℝ≥0}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ)
    (hbound : ∀ x, f x ∈ Metric.closedBall (f (γ 0)) r → ∀ v : TangentSpace I x,
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f x v)‖ₑ ≤ C * ‖v‖ₑ)
    (hshort : (C : ℝ≥0∞) * pathELength I γ 0 1 < r) :
    ∀ t ∈ Icc (0 : ℝ) 1, f (γ t) ∈ Metric.closedBall (f (γ 0)) r := by
  let A := {t : ℝ | f (γ t) ∈ Metric.closedBall (f (γ 0)) r}
  have hA : IsClosed (A ∩ Icc 0 1) :=
    ((Metric.isClosed_closedBall).preimage (hf.continuous.comp hγ.continuous)).inter isClosed_Icc
  have hzero : (0 : ℝ) ∈ A := Metric.mem_closedBall_self r.coe_nonneg
  apply hA.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hzero
  intro t ht hAt
  have hvariation := coordinate_edist_le_mul_pathELength hf hγ ht.1
    (fun u hu => hbound (γ u) (hAt hu))
  have hlength : (C : ℝ≥0∞) * pathELength I γ 0 t ≤ C * pathELength I γ 0 1 := by
    gcongr
    exact ht.2.le
  have hlt : edist (f (γ 0)) (f (γ t)) < r := hvariation.trans_lt
    (hlength.trans_lt hshort)
  have hball : f (γ t) ∈ Metric.ball (f (γ 0)) r := by
    rw [← Metric.eball_coe, Metric.mem_eball, edist_comm]
    exact hlt
  have hnhds : {u | f (γ u) ∈ Metric.ball (f (γ 0)) r} ∈ 𝓝 t :=
    (Metric.isOpen_ball.preimage (hf.continuous.comp hγ.continuous)).mem_nhds hball
  exact Filter.mem_of_superset (nhdsWithin_le_nhds hnhds)
    (fun u hu => Metric.ball_subset_closedBall hu)

theorem coordinate_edist_le_of_short_path {f : M → F} {C r : ℝ≥0}
    (hf : ContMDiff I 𝓘(ℝ, F) 1 f) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ)
    (hbound : ∀ x, f x ∈ Metric.closedBall (f (γ 0)) r → ∀ v : TangentSpace I x,
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f x v)‖ₑ ≤ C * ‖v‖ₑ)
    (hshort : (C : ℝ≥0∞) * pathELength I γ 0 1 < r) :
    edist (f (γ 0)) (f (γ 1)) ≤ C * pathELength I γ 0 1 :=
  coordinate_edist_le_mul_pathELength hf hγ zero_le_one
    (fun t ht => hbound (γ t) (coordinate_path_stays_in_closedBall hf hγ hbound hshort t ht))

end Erdos3

end

section

namespace Erdos3

open Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal NNReal Bundle Topology

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)] [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]

theorem coordinate_edist_le_of_riemannianEDist_lt {f : M → F} {C r : ℝ≥0}
    (hC : 0 < C) (hf : ContMDiff I 𝓘(ℝ, F) 1 f) (x y : M)
    (hbound : ∀ z, f z ∈ Metric.closedBall (f x) r → ∀ v : TangentSpace I z,
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f z v)‖ₑ ≤ C * ‖v‖ₑ)
    (hnear : (C : ℝ≥0∞) * riemannianEDist I x y < r) :
    edist (f x) (f y) ≤ C * riemannianEDist I x y := by
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  have hCt : (C : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  apply le_of_forall_gt
  intro q hq
  have hmin : (C : ℝ≥0∞) * riemannianEDist I x y < min q r := lt_min hq hnear
  have hinput : riemannianEDist I x y < min q r / C := by
    apply (ENNReal.lt_div_iff_mul_lt (.inl hC0) (.inl hCt)).mpr
    simpa only [mul_comm] using hmin
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hinput zero_lt_one
  have hmul : (C : ℝ≥0∞) * pathELength I γ 0 1 < min q r := by
    simpa only [mul_comm] using
      (ENNReal.lt_div_iff_mul_lt (.inl hC0) (.inl hCt)).mp hlen
  have hb : ∀ z, f z ∈ Metric.closedBall (f (γ 0)) r → ∀ v : TangentSpace I z,
      ‖tangentModelVector (mfderiv I 𝓘(ℝ, F) f z v)‖ₑ ≤ C * ‖v‖ₑ := by
    simpa only [hγ0] using hbound
  have hv := coordinate_edist_le_of_short_path hf hγ hb (hmul.trans_le (min_le_right q r))
  rw [hγ0, hγ1] at hv
  exact hv.trans_lt (hmul.trans_le (min_le_left q r))

end Erdos3

end

end OAI
