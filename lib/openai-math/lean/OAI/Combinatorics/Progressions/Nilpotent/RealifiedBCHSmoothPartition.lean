import OAI.Combinatorics.Progressions.Geometry.MetricOpenCharts
import OAI.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

theorem exists_realification_quotient_chart_metric_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ)
      (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l),
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := realificationQuotientMetricSpace e Γ l hl houter
      let G := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
      let ΓR : Subgroup G := Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
          ∀ z : G,
            (∀ i, |(e.baseChange ℝ).repr z.coord i| ≤ Real.exp ((p + 2) ^ a)) →
            ∀ v w : ι → ℝ, (∀ i, |v i| ≤ r) → (∀ i, |w i| ≤ r) →
              let q := fun u => (QuotientGroup.mk
                (z * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm u) : G ⧸ ΓR)
              dist (q v) (q w) ≤ K * dist v w ∧ dist v w ≤ K * dist (q v) (q w) := by
  obtain ⟨D, hD, hchart⟩ := NilpotentLieBCHGroup.exists_uniform_quotient_chart_metric_exp_bound s a
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl houter hc hp hd hH hlp
  exact hchart (e.baseChange ℝ) (lieStructureConstants e) H p
    (realification_lowerCentralSeries_eq_bot hnil) (Γ.map NilpotentLieBCHGroup.realificationHom)
    (NilpotentLieBCHGroup.realification_subgroup_closed_discrete e Γ l hl houter).1 l hl
    (NilpotentLieBCHGroup.realification_subgroup_grid e Γ l houter)
    (fun i j k => (realLieBasis_structure e i j k).symm) hc hp hd hH hlp

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

theorem exists_realification_bilipschitz_charts_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ)
      (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l),
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := realificationQuotientMetricSpace e Γ l hl houter
      let G := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
      let ΓR : Subgroup G := Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
          ∀ z : G, (∀ i, |(e.baseChange ℝ).repr z.coord i| ≤ Real.exp ((p + 2) ^ a)) →
            ∃ φ : OpenPartialHomeomorph (ι → ℝ) (G ⧸ ΓR),
              (∀ v, φ v = (QuotientGroup.mk
                (z * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v) : G ⧸ ΓR)) ∧
              φ.source = {v | ∀ i, |v i| < r} ∧
              LipschitzOnWith K φ φ.source ∧ LipschitzOnWith K φ.symm φ.target := by
  obtain ⟨D, hD, hmetric⟩ := exists_realification_quotient_chart_metric_exp_bound s a
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl houter hc hp hd hH hlp
  let := realificationQuotientMetricSpace e Γ l hl houter
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (e.baseChange ℝ).finiteDimensional_of_finite
  obtain ⟨r, hr, hr1, hrp, K, hK, hcharts⟩ := hmetric e hnil Γ l H p hl houter hc hp hd hH hlp
  refine ⟨r, hr, hr1, hrp, K, hK, ?_⟩
  intro z hz
  let q := fun v : ι → ℝ => (QuotientGroup.mk
    (z * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v) :
      _ ⧸ Γ.map NilpotentLieBCHGroup.realificationHom)
  have hq : Continuous q := QuotientGroup.continuous_mk.comp
    (continuous_const.mul (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm.continuous)
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe.comp
    ((Homeomorph.mulLeft z).isOpenMap.comp (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm.isOpenMap)
  have hU : IsOpen {v : ι → ℝ | ∀ i, |v i| < r} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (continuous_apply i).abs continuous_const)
  obtain ⟨φ, hφ, hsource, _, hLip, hInv⟩ := exists_openPartialHomeomorph_of_metric_bounds q hq hqo
    {v : ι → ℝ | ∀ i, |v i| < r} hU K
    (fun v hv w hw => (hcharts z hz v w (fun i => (hv i).le) (fun i => (hw i).le)).1)
    (fun v hv w hw => (hcharts z hz v w (fun i => (hv i).le) (fun i => (hw i).le)).2)
  exact ⟨φ, hφ, hsource, hLip, hInv⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

theorem exists_realification_finite_bilipschitz_atlas_exp_bound (s : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ)
      (hl : 0 < l) (_hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
      (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l),
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := realificationQuotientMetricSpace e Γ l hl houter
      let G := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
      let ΓR : Subgroup G := Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ centers : Fin n → G, ∃ φ : Fin n → OpenPartialHomeomorph (ι → ℝ) (G ⧸ ΓR),
          (∀ j i, |(e.baseChange ℝ).repr (centers j).coord i| ≤ Real.exp ((p + D) ^ D)) ∧
          (∀ j v, φ j v = (QuotientGroup.mk
            (centers j * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v) : G ⧸ ΓR)) ∧
          (∀ j, (φ j).source = {v | ∀ i, |v i| < r}) ∧
          (∀ j, LipschitzOnWith K (φ j) (φ j).source) ∧
          (∀ j, LipschitzOnWith K (φ j).symm (φ j).target) ∧
          (∀ x : G ⧸ ΓR, ∃ j, ∃ u : ι → ℝ, (∀ i, |u i| ≤ r / 2) ∧ φ j u = x) := by
  obtain ⟨C₀, hC₀, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨C₁, hC₁, hcharts⟩ := exists_realification_bilipschitz_charts_exp_bound s C₀
  let Cᵣ := C₀ + C₁ + 2
  have hCᵣ : 2 ≤ Cᵣ := by dsimp [Cᵣ]; omega
  obtain ⟨C₂, hC₂, hcount⟩ := exists_bch_flexible_cover_exp_bound s C₀ Cᵣ hC₀ hCᵣ
  let D := Cᵣ + C₂ + 2
  have hD : 2 ≤ D := by dsimp [D]; omega
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl hinner houter hc hp hd hH hlp
  let := realificationQuotientMetricSpace e Γ l hl houter
  have hpq : 0 ≤ p + C₀ := by positivity
  have hdq : (Fintype.card ι : ℝ) ≤ p + C₀ := hd.trans (by linarith [Nat.cast_nonneg (α := ℝ) C₀])
  have hep : Real.exp p ≤ Real.exp (p + C₀) := Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) C₀])
  obtain ⟨r, hr, hr1, hrp, K, hKp, hcharts⟩ :=
    hcharts e hnil Γ l H (p + C₀) hl houter hc hpq hdq (hH.trans hep) (hlp.trans hep)
  have hshift : Real.exp (((p + C₀) + C₁) ^ C₁) ≤ Real.exp ((p + Cᵣ) ^ Cᵣ) :=
    Real.exp_le_exp.mpr (shifted_center_power_bound C₀ C₁ hp)
  have hrC := hrp.trans hshift
  have hKC := hKp.trans hshift
  have hRD := Real.exp_le_exp.mpr (shifted_power_self_mono (C := Cᵣ) (D := D)
    hp (by omega) (by dsimp [D]; omega))
  let B := Real.exp ((p + C₀) ^ C₀)
  have hB : 1 ≤ B := Real.one_le_exp (by positivity)
  have hBD : B ≤ Real.exp ((p + D) ^ D) := Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := C₀) (D := D) hp (by omega) (by dsimp [D, Cᵣ]; omega))
  have hBZ : B ≤ Real.exp (((p + C₀) + 2) ^ C₀) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) C₀)
  obtain ⟨centers, hcenters, hcover⟩ := NilpotentLieBCHGroup.finite_quotient_coordinate_cover
    (e.baseChange ℝ) (lieStructureConstants e) (fun i j k => (realLieBasis_structure e i j k).symm) hc
    (Γ.map NilpotentLieBCHGroup.realificationHom) B hB
    (hrep e hnil Γ l H p hl hinner hc hp hd hH hlp) r hr
  choose φ hφ hsource hLip hInv using fun j => hcharts (centers j) (fun i => (hcenters j i).trans hBZ)
  have hn := (hcount (Fintype.card ι) H p r hp hd hH hr hrC).trans
    (Real.exp_le_exp.mpr (shifted_power_self_mono (C := C₂) (D := D)
      hp (by omega) (by dsimp [D]; omega)))
  refine ⟨r, hr, hr1, hrC.trans hRD, K, hKC.trans hRD, _, by positivity, hn,
    centers, φ, fun j i => (hcenters j i).trans hBD, hφ, hsource, hLip, hInv, ?_⟩
  intro x
  obtain ⟨j, u, hu, heq⟩ := hcover x
  exact ⟨j, u, hu, (hφ j u).trans heq⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal Manifold ContDiff

theorem exists_realification_smooth_partition_exp_bound (s : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ)
      (hl : 0 < l) (_hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
      (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
      (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := realificationQuotientMetricSpace e Γ l hl houter
      letI := realificationQuotientChartedSpace e Γ l hl houter hc
      let G := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
      let ΓR : Subgroup G := Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ r : ℝ≥0, 0 < r ∧ r ≤ 1 ∧ 1 / (r : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ centers : Fin n → G, ∃ φ : Fin n → OpenPartialHomeomorph (ι → ℝ) (G ⧸ ΓR),
          (∀ j i, |(e.baseChange ℝ).repr (centers j).coord i| ≤ Real.exp ((p + D) ^ D)) ∧
          (∀ j v, φ j v = (QuotientGroup.mk
            (centers j * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v) : G ⧸ ΓR)) ∧
          (∀ j, (φ j).source = {v | ∀ i, |v i| < (r : ℝ)}) ∧
          (∀ j, (φ j).symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, ι → ℝ) ∞ (G ⧸ ΓR)) ∧
          ∃ P : ℝ≥0, (P : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
          ∃ f : Fin n → (G ⧸ ΓR) → ℝ,
            (∀ j x, 0 ≤ f j x ∧ f j x ≤ 1) ∧ (∀ x, ∑ j, f j x = 1) ∧
            (∀ j, HasCompactSupport (f j) ∧ tsupport (f j) ⊆ (φ j).target) ∧
            (∀ j, ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ℝ) ∞ (f j)) ∧
            (∀ j, LipschitzWith P (f j)) ∧
            (∀ j, tsupport (f j) ⊆ φ j '' Metric.closedBall 0 (3 * (r : ℝ) / 4)) ∧
            ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
              ∀ j, LipschitzOnWith K (φ j) (φ j).source := by
  obtain ⟨D₀, hD₀, hatlas⟩ := exists_realification_finite_bilipschitz_atlas_exp_bound s
  obtain ⟨D₁, hD₁, hleft⟩ := NilpotentLieBCHGroup.exists_uniform_left_lipschitz_exp_bound s D₀
  obtain ⟨D₂, hD₂, hinverse⟩ := exists_bchInverseBoxConstant_exp_bound s 0
  obtain ⟨A, _, hcutoff⟩ := exists_smooth_box_cutoffs
  obtain ⟨N, hN⟩ := exists_nat_ge (A : ℝ)
  let T := D₀ + D₁ + D₂ + N + 5
  let D := T + 21
  have hT : 2 ≤ T := by dsimp [T]; omega
  have hD : 2 ≤ D := by dsimp [D]; omega
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl hinner houter hc hp hd hH hlp
  let := realificationQuotientMetricSpace e Γ l hl houter
  let := realificationQuotientChartedSpace e Γ l hl houter hc
  let := NilpotentLieBCHGroup.basisChartedSpace
    (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ)
  let := NilpotentLieBCHGroup.rightMetricSpace
    (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ)
  obtain ⟨r, hr, hr1, hri, K, hK, n, hn, hnb, centers, φ,
    hcenters, hφ, hsource, hForward, hInv, hcover⟩ :=
    hatlas e hnil Γ l H p hl hinner houter hc hp hd hH hlp
  let rN : ℝ≥0 := ⟨r, hr.le⟩
  have hstructure := fun i j k => (realLieBasis_structure e i j k).symm
  have hpq : 0 ≤ p + D₀ := by positivity
  have hdq : (Fintype.card ι : ℝ) ≤ p + D₀ := hd.trans (by linarith [Nat.cast_nonneg (α := ℝ) D₀])
  have hHq : (H : ℝ) ≤ Real.exp (p + D₀) :=
    hH.trans (Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) D₀]))
  obtain ⟨C, hC, hCb, hleft⟩ := hleft (e.baseChange ℝ) (lieStructureConstants e) H (p + D₀)
    (realification_lowerCentralSeries_eq_bot hnil) hstructure hpq hdq hHq hc
  have hcenterInv (j) : LipschitzWith C (fun x => (centers j)⁻¹ * x) := by
    apply hleft
    intro i
    have hi := (hcenters j i).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by positivity) (show p + D₀ ≤ (p + D₀) + 2 by linarith) D₀))
    simpa only [NilpotentLieBCHGroup.coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hi
  have hclosed := (NilpotentLieBCHGroup.realification_subgroup_closed_discrete e Γ l hl houter).1
  obtain ⟨ψ, hsmooth, _, hrange, hone, hzero, hLip⟩ := hcutoff (ι := ι) rN hr
  obtain ⟨f, hfrange, hfsum, hfsupport, hfsmooth, hfLip, hfInner⟩ :=
    NilpotentLieBCHGroup.exists_smooth_quotient_chart_partition (e.baseChange ℝ) (lieStructureConstants e)
      hstructure hc (Γ.map NilpotentLieBCHGroup.realificationHom) hclosed C hC centers hcenterInv
      rN hr hr1 φ K hφ hsource hInv hcover ψ (Fintype.card ι * A / rN) hsmooth hrange hone hzero hLip
  have hmono (B : ℕ) (hB : 2 ≤ B) (hBT : B ≤ T) :
      Real.exp ((p + B) ^ B) ≤ Real.exp ((p + T) ^ T) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hp (by omega) hBT)
  have hDT : D₀ ≤ T := by dsimp [T]; omega
  have h0T := hmono D₀ hD₀ hDT
  have hshift := shifted_center_power_bound D₀ D₁ hp
  have hCT : (C : ℝ) ≤ Real.exp ((p + T) ^ T) :=
    (hCb.trans (Real.exp_le_exp.mpr hshift)).trans
      (hmono (D₀ + D₁ + 2) (by omega) (by dsimp [T]; omega))
  have hBunit : ((1 : ℝ≥0) : ℝ) ≤ Real.exp ((p + 2) ^ 0) := by
    simpa only [NNReal.coe_one, pow_zero] using Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  have hBT : (bchLogMetricConstant s (Fintype.card ι) H 1 : ℝ) ≤ Real.exp ((p + T) ^ T) :=
    (NNReal.coe_le_coe.mpr (bchLogMetricConstant_le_inverseBoxConstant _ _ _)).trans
      ((hinverse _ H 1 p hp hd hH hBunit).trans (hmono D₂ hD₂ (by dsimp [T]; omega)))
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hbase : p + T ≤ (p + T) ^ T := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + T) (by omega : 1 ≤ T)
  have hdT : (Fintype.card ι : ℝ) ≤ Real.exp ((p + T) ^ T) := by
    linarith [Real.add_one_le_exp ((p + T) ^ T)]
  have hAT : (A : ℝ) ≤ Real.exp ((p + T) ^ T) := by
    have hNT : (N : ℝ) ≤ T := by exact_mod_cast (show N ≤ T by dsimp [T]; omega)
    linarith [Real.add_one_le_exp ((p + T) ^ T)]
  let P : ℝ≥0 := (n + 1) * ((Fintype.card ι * A / rN) * K +
    1 / (rN / (4 * (C * bchLogMetricConstant s (Fintype.card ι) H 1 ^ 2))))
  have hP : (P : ℝ) ≤ Real.exp ((p + D) ^ D) :=
    smooth_partition_power_budget T n (Fintype.card ι) hT A K C _ rN hp
      (hnb.trans h0T) hdT hAT (hK.trans h0T) hCT hBT (hri.trans h0T)
  have h0D : Real.exp ((p + D₀) ^ D₀) ≤ Real.exp ((p + D) ^ D) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hp (by omega) (by dsimp [D]; omega))
  refine ⟨rN, hr, hr1, hri.trans h0D, n, hn, hnb.trans h0D, centers, φ,
    fun j i => (hcenters j i).trans h0D, hφ, hsource, ?_, P, hP, f,
    hfrange, hfsum, hfsupport, ?_, ?_, hfInner, K, hK.trans h0D, hForward⟩
  · exact fun j => realification_quotient_chart_mem_maximalAtlas e Γ l hl houter hc
      (centers j) (φ j) (hφ j) ∞
  · exact fun j => (contMDiff_realification_quotient_iff e Γ l hl houter hc ∞ (f j)).mpr (hfsmooth j)
  · simpa only [Fintype.card_fin] using hfLip

end Erdos3

end

end OAI
