import OAI.Combinatorics.Progressions.Estimates.AmbientImageExtension
import OAI.Combinatorics.Progressions.Estimates.NormalizedCutoffs
import OAI.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Set
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem ball_subset_quotient_coordinate_image
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) :
    letI := rightMetricSpace (hnil := hnil) e
    ∀ C : ℝ≥0, 0 < C → ∀ z : NilpotentLieBCHGroup L s hnil,
      LipschitzWith C (fun x => z⁻¹ * x) → ∀ r : ℝ, 0 < r → r ≤ 1 →
        letI := quotientMetricSpace e Γ hΓ
        let M := C * (bchLogMetricConstant s (Fintype.card ι) H 1) ^ 2
        let q := fun u => (QuotientGroup.mk (z * (basisHomeomorph e).symm u) : _ ⧸ Γ)
        ∀ v : ι → ℝ, (∀ i, |v i| ≤ 3 * r / 4) →
          Metric.ball (q v) (r / (4 * (M : ℝ))) ⊆ q '' {u | ∀ i, |u i| < r} := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  intro C hC z hleft r hr hr1
  let := quotientMetricSpace e Γ hΓ
  dsimp only
  intro v hv x hx
  let C₀ := bchLogMetricConstant s (Fintype.card ι) H 1
  let M : ℝ≥0 := C * C₀ ^ 2
  have hC' : (0 : ℝ) < C := hC
  have hC₀ : (1 : ℝ) ≤ C₀ := one_le_bchLogMetricConstant _ _ _ _
  have hM : (0 : ℝ) < M := by
    change 0 < (C : ℝ) * (C₀ : ℝ) ^ 2
    positivity
  obtain ⟨g, hg, hquot⟩ := rightCosetMetricSpace_exists_lift Γ hΓ
    (z * (basisHomeomorph e).symm v) (r / (4 * (M : ℝ))) x hx
  let a := (basisHomeomorph (hnil := hnil) e).symm v
  let b := z⁻¹ * g
  have hab : dist a b ≤ (C : ℝ) * dist g (z * a) := by
    have ht := hleft.dist_le_mul (z * a) g
    simpa only [inv_mul_cancel_left, dist_comm] using ht
  have hsmall : (C₀ : ℝ) ^ 2 * dist a b < r / 4 := by
    calc
      _ ≤ (C₀ : ℝ) ^ 2 * ((C : ℝ) * dist g (z * a)) :=
        mul_le_mul_of_nonneg_left hab (sq_nonneg _)
      _ = (M : ℝ) * dist g (z * a) := by simp only [M, NNReal.coe_mul, NNReal.coe_pow]; ring
      _ < r / 4 := by
        have ht := (lt_div_iff₀ (by positivity : 0 < 4 * (M : ℝ))).mp hg
        apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
        nlinarith
  have hnear : (C₀ : ℝ) * dist a b < 1 := by
    have hsq : (C₀ : ℝ) ≤ (C₀ : ℝ) ^ 2 := by nlinarith
    have ht := (mul_le_mul_of_nonneg_right hsq (dist_nonneg (x := a) (y := b))).trans_lt hsmall
    linarith
  have ha (i) : |e.repr a.coord i| ≤ 1 := by
    change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph e).symm v) i| ≤ 1
    rw [Homeomorph.apply_symm_apply]
    linarith [hv i]
  have hcoords := dist_coordinates_le_of_near_unit_box e c hstructure hc a b ha hnear
  have hav : basisHomeomorph e a = v := Homeomorph.apply_symm_apply _ v
  rw [hav] at hcoords
  have hu : ∀ i, |basisHomeomorph e b i| < r := by
    intro i
    have hi := dist_le_pi_dist (basisHomeomorph e a) (basisHomeomorph e b) i
    rw [hav, Real.dist_eq] at hi
    have hb := abs_sub_abs_le_abs_sub (basisHomeomorph e b i) (v i)
    rw [abs_sub_comm] at hb
    have ht := (hi.trans hcoords).trans_lt hsmall
    linarith [hv i]
  refine ⟨basisHomeomorph e b, hu, ?_⟩
  change (QuotientGroup.mk (z * (basisHomeomorph e).symm (basisHomeomorph e b)) : _ ⧸ Γ) = x
  rw [Homeomorph.symm_apply_apply]
  simpa only [b, mul_inv_cancel_left] using hquot

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem lipschitz_quotient_chartCutoff
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) :
    letI := rightMetricSpace (hnil := hnil) e
    ∀ C : ℝ≥0, 0 < C → ∀ z : NilpotentLieBCHGroup L s hnil,
      LipschitzWith C (fun x => z⁻¹ * x) → ∀ r : ℝ≥0, 0 < r → r ≤ 1 →
        letI := quotientMetricSpace e Γ hΓ
        ∀ φ : OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ),
          (∀ v, φ v = QuotientGroup.mk (z * (basisHomeomorph e).symm v)) →
          φ.source = {v | ∀ i, |v i| < (r : ℝ)} →
          ∀ (ψ : (ι → ℝ) → ℝ) (A K : ℝ≥0),
            (∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) →
            (∀ v, (∃ i, 3 * (r : ℝ) / 4 ≤ |v i|) → ψ v = 0) →
            LipschitzWith A ψ → LipschitzOnWith K φ.symm φ.target →
            LipschitzWith (A * K + 1 / (r / (4 * (C * bchLogMetricConstant s (Fintype.card ι) H 1 ^ 2))))
              (chartCutoff φ ψ) := by
  let := rightMetricSpace (hnil := hnil) e
  intro C hC z hleft r hr hr1
  let := quotientMetricSpace e Γ hΓ
  intro φ hφ hsource ψ A K hψ hzero hLip hInv
  let M := C * bchLogMetricConstant s (Fintype.card ι) H 1 ^ 2
  let δ : ℝ≥0 := r / (4 * M)
  have hδ : 0 < δ := by
    exact div_pos hr (mul_pos (by norm_num) (mul_pos hC (pow_pos (bchLogMetricConstant_pos _ _ _ _) _)))
  apply lipschitz_chartCutoff φ ψ A K δ hδ hψ hLip hInv
  intro x hx hn y hy
  have hv (i) : |φ.symm x i| ≤ 3 * (r : ℝ) / 4 := by
    by_contra! hi
    exact hn (hzero _ ⟨i, hi.le⟩)
  have hball := ball_subset_quotient_coordinate_image e c hstructure hc Γ hΓ C hC z hleft
    r hr hr1 (φ.symm x) hv
  have heqx : (QuotientGroup.mk (z * (basisHomeomorph e).symm (φ.symm x)) : _ ⧸ Γ) = x :=
    (hφ _).symm.trans (φ.right_inv hx)
  dsimp only at hball
  rw [heqx] at hball
  by_contra! hd
  have hyball : y ∈ Metric.ball x ((r : ℝ) / (4 * (M : ℝ))) := by
    simpa only [Metric.mem_ball, dist_comm, δ, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat] using hd
  obtain ⟨u, hu, heq⟩ := hball hyball
  apply hy
  have hus : u ∈ φ.source := by rwa [hsource]
  have hym : φ u = y := (hφ u).trans heq
  exact hym ▸ φ.map_source hus

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal Manifold ContDiff

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_smooth_quotient_chart_partition
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) :
    letI := rightMetricSpace (hnil := hnil) e
    ∀ C : ℝ≥0, 0 < C → ∀ centers : κ → NilpotentLieBCHGroup L s hnil,
      (∀ j, LipschitzWith C (fun x => (centers j)⁻¹ * x)) →
      ∀ r : ℝ≥0, 0 < r → r ≤ 1 →
        letI := quotientMetricSpace e Γ hΓ
        letI := basisChartedSpace (hnil := hnil) e
        ∀ (φ : κ → OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ)) (K : ℝ≥0),
          (∀ j v, φ j v = QuotientGroup.mk (centers j * (basisHomeomorph e).symm v)) →
          (∀ j, (φ j).source = {v | ∀ i, |v i| < (r : ℝ)}) →
          (∀ j, LipschitzOnWith K (φ j).symm (φ j).target) →
          (∀ x, ∃ j v, (∀ i, |v i| ≤ (r : ℝ) / 2) ∧ φ j v = x) →
          ∀ (ψ : (ι → ℝ) → ℝ) (A : ℝ≥0), ContDiff ℝ ∞ ψ →
            (∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) →
            (∀ v, (∀ i, |v i| ≤ (r : ℝ) / 2) → ψ v = 1) →
            (∀ v, (∃ i, 3 * (r : ℝ) / 4 ≤ |v i|) → ψ v = 0) → LipschitzWith A ψ →
            let Q := (Fintype.card κ + 1) *
              (A * K + 1 / (r / (4 * (C * bchLogMetricConstant s (Fintype.card ι) H 1 ^ 2))))
            ∃ f : κ → (_ ⧸ Γ) → ℝ,
              (∀ j x, 0 ≤ f j x ∧ f j x ≤ 1) ∧ (∀ x, ∑ j, f j x = 1) ∧
              (∀ j, HasCompactSupport (f j) ∧ tsupport (f j) ⊆ (φ j).target) ∧
              (∀ j, ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ℝ) ∞
                (fun g : NilpotentLieBCHGroup L s hnil => f j (QuotientGroup.mk g))) ∧
              (∀ j, LipschitzWith Q (f j)) ∧
              (∀ j, tsupport (f j) ⊆ φ j '' Metric.closedBall 0 (3 * (r : ℝ) / 4)) := by
  let := rightMetricSpace (hnil := hnil) e
  intro C hC centers hleft r hr hr1
  let := quotientMetricSpace e Γ hΓ
  let := basisChartedSpace (hnil := hnil) e
  intro φ K hφ hsource hInv hcover ψ A hsmooth hrange hone hzero hLip
  dsimp only
  let g := fun j => chartCutoff (φ j) ψ
  have hgpos (j) (x) : 0 ≤ g j x := (chartCutoff_range (φ j) ψ hrange x).1
  have hgrange (j) (x) : 0 ≤ g j x ∧ g j x ≤ 1 := chartCutoff_range (φ j) ψ hrange x
  have hgcover (x) : ∃ j, g j x = 1 := by
    obtain ⟨j, v, hv, rfl⟩ := hcover x
    exact ⟨j, boxChartCutoff_eq_one (φ j) ψ hr (hsource j) hone v hv⟩
  have hgsupport (j) : HasCompactSupport (g j) ∧ tsupport (g j) ⊆ (φ j).target :=
    boxChartCutoff_support (φ j) ψ hr (hsource j) hzero
  have hgsmooth (j) : ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun x : NilpotentLieBCHGroup L s hnil => g j (QuotientGroup.mk x)) :=
    contMDiff_quotient_chartCutoff e Γ (centers j) (φ j) (hφ j) ψ hsmooth (hgsupport j).2
  have hgLip (j) := lipschitz_quotient_chartCutoff e c hstructure hc Γ hΓ C hC
    (centers j) (hleft j) r hr hr1 (φ j) (hφ j) (hsource j) ψ A K hrange hzero hLip (hInv j)
  refine ⟨normalizedCutoffs g, normalizedCutoffs_range g hgpos hgcover,
    sum_normalizedCutoffs g hgpos hgcover, ?_, ?_, ?_, ?_⟩
  · intro j
    have hs := tsupport_normalizedCutoffs_subset g j
    exact ⟨(hgsupport j).1.of_isClosed_subset isClosed_closure hs, hs.trans (hgsupport j).2⟩
  · exact fun j => contMDiff_normalizedCutoffs_comp g QuotientGroup.mk hgsmooth hgpos hgcover j
  · exact fun j => lipschitz_normalizedCutoffs g _ hgLip hgrange hgcover j
  · intro j
    exact (tsupport_normalizedCutoffs_subset g j).trans
      (tsupport_chartCutoff_subset (φ j) ψ (isCompact_closedBall _ _)
        (closedBox_subset_chart_source (φ j) hr (hsource j))
        (support_subset_box_of_cutoff ψ hr hzero))

end Erdos3.NilpotentLieBCHGroup

end

end OAI
