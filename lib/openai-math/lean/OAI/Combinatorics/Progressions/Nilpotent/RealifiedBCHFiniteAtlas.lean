import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import OAI.Combinatorics.Progressions.Estimates.ImageRepresentatives

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
  (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)

noncomputable def quotientCoordinateChart (z : NilpotentLieBCHGroup L s hnil) :
    OpenPartialHomeomorph (ι → ℝ) (NilpotentLieBCHGroup L s hnil ⧸ Γ) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let f := fun v : ι → ℝ => (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ)
  let U := {v : ι → ℝ | ∀ i, |v i| < bchInjectivityRadius s (Fintype.card ι) H l}
  have hi : Set.InjOn f U := (quotient_coordinate_injOn e c hstructure hc Γ l hl hgrid z).mono
    (fun _ hx i => (hx i).le)
  have hf : Continuous f := QuotientGroup.continuous_mk.comp
    (continuous_const.mul (basisHomeomorph e).symm.continuous)
  have ho : IsOpenMap f := QuotientGroup.isOpenMap_coe.comp
    ((Homeomorph.mulLeft z).isOpenMap.comp (basisHomeomorph e).symm.isOpenMap)
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (continuous_apply i).abs continuous_const)
  exact OpenPartialHomeomorph.ofContinuousOpen (hi.toPartialEquiv f U) hf.continuousOn ho hU

theorem quotientCoordinateChart_apply (z : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    quotientCoordinateChart e c hstructure hc Γ l hl hgrid z v =
      (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ) := rfl

theorem quotientCoordinateChart_source (z : NilpotentLieBCHGroup L s hnil) :
    (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).source =
      {v : ι → ℝ | ∀ i, |v i| < bchInjectivityRadius s (Fintype.card ι) H l} := rfl

theorem quotientCoordinateChart_target (z : NilpotentLieBCHGroup L s hnil) :
    (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).target =
      (fun v : ι → ℝ => (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ)) ''
        {v : ι → ℝ | ∀ i, |v i| < bchInjectivityRadius s (Fintype.card ι) H l} := rfl

theorem quotientCoordinateChart_center_mem (z : NilpotentLieBCHGroup L s hnil) :
    (QuotientGroup.mk z : _ ⧸ Γ) ∈ (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).target := by
  have hzero : (basisHomeomorph (hnil := hnil) e).symm 0 = 1 := by
    apply (basisHomeomorph e).injective
    simp only [Homeomorph.apply_symm_apply, basisHomeomorph_apply, coord_one, map_zero]
  rw [quotientCoordinateChart_target]
  refine ⟨0, ?_, ?_⟩
  · intro i
    simpa only [Pi.zero_apply, abs_zero] using bchInjectivityRadius_pos s (Fintype.card ι) H l
  · simp only [hzero, mul_one]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

namespace NilpotentLieBCHGroup

theorem quotient_covered_by_coordinate_box {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
    {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℝ)
    (hrep : ∀ g : NilpotentLieBCHGroup L s hnil, ∃ z,
      (∀ i, |e.repr z.coord i| ≤ B) ∧ ∃ γ ∈ Γ, g = z * γ) :
    ∀ x : NilpotentLieBCHGroup L s hnil ⧸ Γ, ∃ v : ι → ℝ,
      (∀ i, |v i| ≤ B) ∧ (QuotientGroup.mk ((basisHomeomorph e).symm v) : _ ⧸ Γ) = x := by
  intro x
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨z, hz, γ, hγ, hg⟩ := hrep g
    refine ⟨basisHomeomorph e z, hz, ?_⟩
    rw [Homeomorph.symm_apply_apply, hg]
    exact (quotient_mk_mul_mem Γ z ⟨γ, hγ⟩).symm

end NilpotentLieBCHGroup

theorem exists_realification_metric_partition_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ)
      (hl : 0 < l) (_hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
      (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l),
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      ∀ r : ℝ≥0, 0 < r → 1 / (r : ℝ) ≤ Real.exp ((p + 2) ^ a) →
      letI := realificationQuotientMetricSpace e Γ l hl houter
      let Q := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) ⧸
        Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ c : Fin n → Q, ∃ ψ : Fin n → Q → ℝ,
          (∀ i x, 0 ≤ ψ i x ∧ ψ i x ≤ 1) ∧
          (∀ x, ∑ i, ψ i x = 1) ∧
          (∀ i x, 2 * (r : ℝ) ≤ dist x (c i) → ψ i x = 0) ∧
          (∀ i, LipschitzWith K (ψ i)) := by
  obtain ⟨C₀, hC₀, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨C, hC, hbudget⟩ := exists_bch_partition_input_exp_bound s a C₀ hC₀
  refine ⟨C + 8, by omega, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl hinner houter hc hp hd hH hlp r hr hrp
  let := realificationQuotientMetricSpace e Γ l hl houter
  let B : ℝ≥0 := ⟨Real.exp ((p + C₀) ^ C₀), Real.exp_nonneg _⟩
  let K := bchBoxMetricConstant s (Fintype.card ι) H B
  have hB1 : 1 ≤ B := Real.one_le_exp (by positivity)
  obtain ⟨hBp, hKp, hrbound⟩ := hbudget (Fintype.card ι) H p hp hd hH
  let f := fun v : ι → ℝ =>
    (QuotientGroup.mk ((NilpotentLieBCHGroup.basisHomeomorph
      (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ)).symm v) :
      _ ⧸ Γ.map NilpotentLieBCHGroup.realificationHom)
  have hf : LipschitzOnWith K f {v | ∀ i, |v i| ≤ B} :=
    NilpotentLieBCHGroup.lipschitzOn_quotient_basisHomeomorph_symm_box (e.baseChange ℝ)
      (lieStructureConstants e) (fun i j k => (realLieBasis_structure e i j k).symm) hc
      (Γ.map NilpotentLieBCHGroup.realificationHom)
      (NilpotentLieBCHGroup.realification_subgroup_closed_discrete e Γ l hl houter).1 B hB1
  have hcover : ∀ x, ∃ v : ι → ℝ, (∀ i, |v i| ≤ B) ∧ f v = x :=
    NilpotentLieBCHGroup.quotient_covered_by_coordinate_box (e.baseChange ℝ)
      (Γ.map NilpotentLieBCHGroup.realificationHom) B
      (hrep e hnil Γ l H p hl hinner hc hp hd hH hlp)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    exists_metric_partition_exp_bound f (Real.exp_pos _) hf hcover r hr C hC hp hd hBp hKp
      (hrp.trans hrbound)

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Set Manifold
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)
  (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
  (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)

@[instance_reducible]
noncomputable def quotientChartedSpace : ChartedSpace (ι → ℝ) (NilpotentLieBCHGroup L s hnil ⧸ Γ) where
  atlas := Set.range (fun z => (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).symm)
  chartAt := fun x => (quotientCoordinateChart e c hstructure hc Γ l hl hgrid x.out).symm
  mem_chart_source := fun x => by
    simpa only [OpenPartialHomeomorph.symm_source, QuotientGroup.out_eq'] using
      quotientCoordinateChart_center_mem e c hstructure hc Γ l hl hgrid x.out
  chart_mem_atlas := fun x => ⟨x.out, rfl⟩

theorem quotientChartedSpace_chartAt (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := quotientChartedSpace e c hstructure hc Γ l hl hgrid
    chartAt (ι → ℝ) x = (quotientCoordinateChart e c hstructure hc Γ l hl hgrid x.out).symm := rfl

theorem quotientCoordinateChart_mem_atlas (z : NilpotentLieBCHGroup L s hnil) :
    letI := quotientChartedSpace e c hstructure hc Γ l hl hgrid
    (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z).symm ∈
      atlas (ι → ℝ) (NilpotentLieBCHGroup L s hnil ⧸ Γ) := ⟨z, rfl⟩

theorem isManifold_quotient (n : ℕ∞ω) :
    letI := quotientChartedSpace e c hstructure hc Γ l hl hgrid
    IsManifold 𝓘(ℝ, ι → ℝ) n (NilpotentLieBCHGroup L s hnil ⧸ Γ) := by
  let := quotientChartedSpace e c hstructure hc Γ l hl hgrid
  apply isManifold_of_contDiffOn
  intro φ ψ hφ hψ
  obtain ⟨z, rfl⟩ := hφ
  obtain ⟨w, rfl⟩ := hψ
  simpa only [OpenPartialHomeomorph.symm_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    preimage_id, range_id, inter_univ] using
    contDiffOn_quotient_chart_transition e Γ z w
      (quotientCoordinateChart e c hstructure hc Γ l hl hgrid z)
      (quotientCoordinateChart e c hstructure hc Γ l hl hgrid w)
      (quotientCoordinateChart_apply e c hstructure hc Γ l hl hgrid z)
      (quotientCoordinateChart_apply e c hstructure hc Γ l hl hgrid w) n

theorem contMDiff_quotient_mk (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := quotientChartedSpace e c hstructure hc Γ l hl hgrid
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n
      (QuotientGroup.mk : NilpotentLieBCHGroup L s hnil → _ ⧸ Γ) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := basisChartedSpace (hnil := hnil) e
  let := quotientChartedSpace e c hstructure hc Γ l hl hgrid
  intro g
  apply contMDiffAt_iff_target.mpr
  refine ⟨QuotientGroup.continuous_mk.continuousAt, ?_⟩
  have h := contMDiffAt_quotient_chartInverse e Γ (QuotientGroup.mk g : _ ⧸ Γ).out
    (quotientCoordinateChart e c hstructure hc Γ l hl hgrid (QuotientGroup.mk g : _ ⧸ Γ).out)
    (quotientCoordinateChart_apply e c hstructure hc Γ l hl hgrid _) n g
    (by simpa only [QuotientGroup.out_eq'] using
      quotientCoordinateChart_center_mem e c hstructure hc Γ l hl hgrid (QuotientGroup.mk g : _ ⧸ Γ).out)
  simpa only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.coe_toPartialEquiv,
    modelWithCornersSelf_coe, Function.id_comp, quotientChartedSpace_chartAt,
    Function.comp_def, Function.id_def] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_realification_open_charts_exp_bound (s : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ),
      0 < l → bchSubgroupCoordinates e Γ ⊆ denominatorGrid l →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      let G := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
      let ΓR : Subgroup G := Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ φ : G → OpenPartialHomeomorph (ι → ℝ) (G ⧸ ΓR),
          (∀ z v, φ z v = (QuotientGroup.mk
            (z * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v) : G ⧸ ΓR)) ∧
          (∀ z, (φ z).source = {v | ∀ i, |v i| < r}) ∧
          (∀ z, (QuotientGroup.mk z : G ⧸ ΓR) ∈ (φ z).target) := by
  obtain ⟨D, hD, hbudget⟩ := exists_bchInjectivityRadius_inv_exp_bound s
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl houter hc hp hd hH hlp
  let ΓR := Γ.map NilpotentLieBCHGroup.realificationHom
  have hgrid := NilpotentLieBCHGroup.realification_subgroup_grid e Γ l houter
  have hstructure := fun i j k => (realLieBasis_structure e i j k).symm
  refine ⟨bchInjectivityRadius s (Fintype.card ι) H l,
    bchInjectivityRadius_pos _ _ _ _, bchInjectivityRadius_le_one _ _ _ _,
    hbudget _ _ _ _ hp hd hH hlp,
    NilpotentLieBCHGroup.quotientCoordinateChart (e.baseChange ℝ) (lieStructureConstants e)
      hstructure hc ΓR l hl hgrid, ?_, ?_, ?_⟩
  · exact NilpotentLieBCHGroup.quotientCoordinateChart_apply _ _ _ _ _ _ _ _
  · exact NilpotentLieBCHGroup.quotientCoordinateChart_source _ _ _ _ _ _ _ _
  · exact NilpotentLieBCHGroup.quotientCoordinateChart_center_mem _ _ _ _ _ _ _ _

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem inv_mul_coordinates_bound
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (u v : NilpotentLieBCHGroup L s hnil) {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hu : ∀ i, |e.repr u.coord i| ≤ B) (hv : ∀ i, |e.repr v.coord i| ≤ B)
    (huv : ∀ i, |e.repr u.coord i - e.repr v.coord i| ≤ δ) (k : ι) :
    |e.repr (u⁻¹ * v).coord k| ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  simpa only [coord_mul, coord_inv, neg_neg] using
    lieBCH_sub_coordinates_bound e c hstructure hc hnil (-u.coord) (-v.coord) hB hδ
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, abs_neg] using hu i)
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, abs_neg] using hv i)
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, neg_sub_neg, abs_sub_comm] using huv i) k

variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

theorem finite_quotient_coordinate_cover
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (B : ℝ) (hB : 1 ≤ B)
    (hrep : ∀ g : NilpotentLieBCHGroup L s hnil, ∃ z,
      (∀ i, |e.repr z.coord i| ≤ B) ∧ ∃ γ ∈ Γ, g = z * γ)
    (r : ℝ) (hr : 0 < r) :
    let K : ℝ≥0 := ⟨bchBoxCoordinateBound s (Fintype.card ι) H B,
      bchBoxCoordinateBound_nonneg _ _ _ (by linarith)⟩
    let n := (boxCoverMeshCount B K (r / 2) + 1) ^ Fintype.card ι
    ∃ centers : Fin n → NilpotentLieBCHGroup L s hnil,
      (∀ j i, |e.repr (centers j).coord i| ≤ B) ∧
      ∀ x : NilpotentLieBCHGroup L s hnil ⧸ Γ, ∃ j, ∃ u : ι → ℝ,
        (∀ i, |u i| ≤ r / 2) ∧
        (QuotientGroup.mk (centers j * (basisHomeomorph e).symm u) : _ ⧸ Γ) = x := by
  classical
  let K : ℝ≥0 := ⟨bchBoxCoordinateBound s (Fintype.card ι) H B,
    bchBoxCoordinateBound_nonneg _ _ _ (by linarith)⟩
  let N := boxCoverMeshCount B K (r / 2)
  let n := (N + 1) ^ Fintype.card ι
  let I := ι → Fin (N + 1)
  have hN : 0 < N := boxCoverMeshCount_pos _ _ _
  have hcard : Fintype.card I = n := by simp [I, n]
  let reindex : I ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let centers : Fin n → NilpotentLieBCHGroup L s hnil := fun j =>
    (basisHomeomorph e).symm (uniformBoxGrid B N (reindex.symm j))
  have hcenters (j : Fin n) : e.equivFun (centers j).coord = uniformBoxGrid B N (reindex.symm j) :=
    (basisHomeomorph (hnil := hnil) e).apply_symm_apply _
  have hcentersB (j i) : |e.repr (centers j).coord i| ≤ B := by
    have := uniformBoxGrid_mem (ι := ι) (by linarith : 0 ≤ B) hN (reindex.symm j) i
    simpa only [← hcenters j, Basis.equivFun_apply] using this
  refine ⟨centers, hcentersB, ?_⟩
  intro x
  obtain ⟨v, hv, hvx⟩ := quotient_covered_by_coordinate_box e Γ B hrep x
  obtain ⟨k, hk⟩ := exists_uniformBoxGrid_approx (by linarith : 0 < B) hN v hv
  let j := reindex k
  let g := (basisHomeomorph (hnil := hnil) e).symm v
  have hgv : e.equivFun g.coord = v := (basisHomeomorph (hnil := hnil) e).apply_symm_apply v
  have hgB (i) : |e.repr g.coord i| ≤ B := by
    simpa only [← hgv, Basis.equivFun_apply] using hv i
  have hdiff (i) : |e.repr (centers j).coord i - e.repr g.coord i| ≤ 2 * B / N := by
    have hi := (dist_pi_le_iff (by positivity : 0 ≤ 2 * B / (N : ℝ))).mp hk i
    have hj : reindex.symm j = k := reindex.symm_apply_apply k
    have hci : e.repr (centers j).coord i = uniformBoxGrid B N k i := by
      simpa only [Basis.equivFun_apply, hj] using congrFun (hcenters j) i
    have hgi : e.repr g.coord i = v i := by
      simpa only [Basis.equivFun_apply] using congrFun hgv i
    simpa only [Real.dist_eq, ← hci, ← hgi, abs_sub_comm] using hi
  have herror : (K : ℝ) * (2 * B / N) ≤ r / 2 := boxCoverMeshCount_error K (by linarith)
  have hsmall (i) : |e.repr ((centers j)⁻¹ * g).coord i| ≤ r / 2 :=
    (inv_mul_coordinates_bound e c hstructure hc (centers j) g hB
      (by positivity) (hcentersB j) hgB hdiff i).trans herror
  refine ⟨j, basisHomeomorph e ((centers j)⁻¹ * g), hsmall, ?_⟩
  simp only [Homeomorph.symm_apply_apply, mul_inv_cancel_left]
  exact hvx

theorem finite_quotient_coordinate_chart_cover
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)
    (B : ℝ) (hB : 1 ≤ B)
    (hrep : ∀ g : NilpotentLieBCHGroup L s hnil, ∃ z,
      (∀ i, |e.repr z.coord i| ≤ B) ∧ ∃ γ ∈ Γ, g = z * γ) :
    let r := bchInjectivityRadius s (Fintype.card ι) H l
    let K : ℝ≥0 := ⟨bchBoxCoordinateBound s (Fintype.card ι) H B,
      bchBoxCoordinateBound_nonneg _ _ _ (by linarith)⟩
    let n := (boxCoverMeshCount B K (r / 2) + 1) ^ Fintype.card ι
    ∃ centers : Fin n → NilpotentLieBCHGroup L s hnil,
      (∀ j i, |e.repr (centers j).coord i| ≤ B) ∧
      ∀ x : NilpotentLieBCHGroup L s hnil ⧸ Γ, ∃ j,
        x ∈ (quotientCoordinateChart e c hstructure hc Γ l hl hgrid (centers j)).target := by
  let r := bchInjectivityRadius s (Fintype.card ι) H l
  have hr : 0 < r := bchInjectivityRadius_pos _ _ _ _
  obtain ⟨centers, hcenters, hcover⟩ :=
    finite_quotient_coordinate_cover e c hstructure hc Γ B hB hrep r hr
  refine ⟨centers, hcenters, ?_⟩
  intro x
  obtain ⟨j, u, hu, heq⟩ := hcover x
  refine ⟨j, ?_⟩
  rw [quotientCoordinateChart_target]
  exact ⟨u, fun i => (hu i).trans_lt (by linarith), heq⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Set Manifold
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem quotient_chart_transition_mem_contDiffGroupoid
    (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (z w : NilpotentLieBCHGroup L s hnil) (φ ψ : OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ))
    (hφ : ∀ v, φ v = QuotientGroup.mk (z * (basisHomeomorph e).symm v))
    (hψ : ∀ v, ψ v = QuotientGroup.mk (w * (basisHomeomorph e).symm v)) (n : ℕ∞ω) :
    φ.trans ψ.symm ∈ contDiffGroupoid n 𝓘(ℝ, ι → ℝ) := by
  simp only [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    preimage_id, range_id, inter_univ]
  constructor
  · exact contDiffOn_quotient_chart_transition e Γ z w φ ψ hφ hψ n
  · exact contDiffOn_quotient_chart_transition e Γ w z ψ φ hψ hφ n

theorem quotient_chart_mem_maximalAtlas
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l)
    (z : NilpotentLieBCHGroup L s hnil) (φ : OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ))
    (hφ : ∀ v, φ v = QuotientGroup.mk (z * (basisHomeomorph e).symm v)) (n : ℕ∞ω) :
    letI := quotientChartedSpace e c hstructure hc Γ l hl hgrid
    φ.symm ∈ IsManifold.maximalAtlas 𝓘(ℝ, ι → ℝ) n (NilpotentLieBCHGroup L s hnil ⧸ Γ) := by
  let := quotientChartedSpace e c hstructure hc Γ l hl hgrid
  intro ψ hψ
  obtain ⟨w, rfl⟩ := hψ
  constructor
  · simpa only [OpenPartialHomeomorph.symm_symm] using
      quotient_chart_transition_mem_contDiffGroupoid e Γ z w φ
        (quotientCoordinateChart e c hstructure hc Γ l hl hgrid w) hφ
        (quotientCoordinateChart_apply e c hstructure hc Γ l hl hgrid w) n
  · simpa only [OpenPartialHomeomorph.symm_symm] using
      quotient_chart_transition_mem_contDiffGroupoid e Γ w z
        (quotientCoordinateChart e c hstructure hc Γ l hl hgrid w) φ
        (quotientCoordinateChart_apply e c hstructure hc Γ l hl hgrid w) hφ n

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped NNReal

theorem exists_bch_chart_cover_exp_bound (s C₀ : ℕ) (hC₀ : 2 ≤ C₀) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ (d H l : ℕ) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      let B := Real.exp ((p + C₀) ^ C₀)
      let r := bchInjectivityRadius s d H l
      let K : ℝ≥0 := ⟨bchBoxCoordinateBound s d H B,
        bchBoxCoordinateBound_nonneg _ _ _ (Real.exp_nonneg _)⟩
      (((boxCoverMeshCount B K (r / 2) + 1) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
      B ≤ Real.exp ((p + D) ^ D) ∧ 1 / r ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C₁, hC₁, hinput⟩ := exists_bch_partition_input_exp_bound s 0 C₀ hC₀
  obtain ⟨C₂, hC₂, hradius⟩ := exists_bchInjectivityRadius_inv_exp_bound s
  let C := C₁ + C₂ + 5
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C + 5, by omega, ?_⟩
  intro d H l p hp hd hH hl
  let B := Real.exp ((p + C₀) ^ C₀)
  let r := bchInjectivityRadius s d H l
  let K : ℝ≥0 := ⟨bchBoxCoordinateBound s d H B,
    bchBoxCoordinateBound_nonneg _ _ _ (Real.exp_nonneg _)⟩
  have hr : 0 < r := bchInjectivityRadius_pos _ _ _ _
  obtain ⟨hB, hmetric, _⟩ := hinput d H p hp hd hH
  have hshift₁ := Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := C₁) (D := C) hp (by omega) (by dsimp [C]; omega))
  have hBC : B ≤ Real.exp ((p + C) ^ C) := hB.trans hshift₁
  have hKC : (K : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    apply le_trans ?_ (hmetric.trans hshift₁)
    change bchBoxCoordinateBound s d H B ≤ ((d : ℝ) + 1) * bchBoxCoordinateBound s d H B
    have := bchBoxCoordinateBound_nonneg s d H (Real.exp_nonneg ((p + C₀) ^ C₀))
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hthree := metricPartition_constant_power_budget C₂ 1 hC₂ ⟨r, hr.le⟩ hp
    (by simpa only [Nat.cast_one] using Real.one_le_exp (by positivity : 0 ≤ (p + C₂) ^ C₂))
    (hradius d H l p hp hd hH hl)
  have hhalf : 1 / (r / 2) ≤ Real.exp ((p + (C₂ + 3 : ℕ)) ^ (C₂ + 3)) := by
    have ht : 3 / r ≤ Real.exp ((p + (C₂ + 3 : ℕ)) ^ (C₂ + 3)) := by
      norm_num at hthree ⊢
      exact hthree
    apply le_trans ?_ ht
    rw [show 1 / (r / 2) = 2 / r by ring]
    exact div_le_div_of_nonneg_right (by norm_num) hr.le
  have hhalfC := hhalf.trans (Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := C₂ + 3) (D := C) hp (by omega) (by dsimp [C]; omega)))
  have hfinal := Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := C) (D := C + 5) hp (by omega) (by omega))
  refine ⟨?_, hBC.trans hfinal, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_ofNat] using
      boxCoverCount_le_exp C d hC K (Real.exp_nonneg _) (by linarith) hp hd hBC hKC hhalfC
  · apply le_trans ?_ (hhalfC.trans hfinal)
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith : 0 < r / 2) (by linarith)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem half_radius_inverse_power_bound (C : ℕ) (hC : 2 ≤ C) {r p : ℝ}
    (hr : 0 < r) (hp : 0 ≤ p) (hri : 1 / r ≤ Real.exp ((p + C) ^ C)) :
    1 / (r / 2) ≤ Real.exp ((p + (C + 3 : ℕ)) ^ (C + 3)) := by
  have h := metricPartition_constant_power_budget C 1 hC ⟨r, hr.le⟩ hp
    (by simpa only [Nat.cast_one] using Real.one_le_exp (by positivity : 0 ≤ (p + C) ^ C)) hri
  have hthree : 3 / r ≤ Real.exp ((p + (C + 3 : ℕ)) ^ (C + 3)) := by
    norm_num at h ⊢
    exact h
  apply le_trans ?_ hthree
  rw [show 1 / (r / 2) = 2 / r by ring]
  exact div_le_div_of_nonneg_right (by norm_num) hr.le

theorem shifted_center_power_bound (A B : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ((p + A) + B) ^ B ≤ (p + (A + B + 2 : ℕ)) ^ (A + B + 2) := by
  have hbase : (p + A) + B ≤ p + (A + B + 2 : ℕ) := by push_cast; linarith
  apply (pow_le_pow_left₀ (by positivity) hbase B).trans
  exact pow_le_pow_right₀
    (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) A, Nat.cast_nonneg (α := ℝ) B]) (by omega)

theorem exists_bch_flexible_cover_exp_bound (s C₀ Cᵣ : ℕ) (hC₀ : 2 ≤ C₀) (hCᵣ : 2 ≤ Cᵣ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ (d H : ℕ) (p r : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      0 < r → 1 / r ≤ Real.exp ((p + Cᵣ) ^ Cᵣ) →
      let B := Real.exp ((p + C₀) ^ C₀)
      let K : ℝ≥0 := ⟨bchBoxCoordinateBound s d H B,
        bchBoxCoordinateBound_nonneg _ _ _ (Real.exp_nonneg _)⟩
      (((boxCoverMeshCount B K (r / 2) + 1) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C₁, hC₁, hinput⟩ := exists_bch_partition_input_exp_bound s 0 C₀ hC₀
  let C := C₁ + Cᵣ + 5
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C + 5, by omega, ?_⟩
  intro d H p r hp hd hH hr hri
  let B := Real.exp ((p + C₀) ^ C₀)
  let K : ℝ≥0 := ⟨bchBoxCoordinateBound s d H B,
    bchBoxCoordinateBound_nonneg _ _ _ (Real.exp_nonneg _)⟩
  obtain ⟨hB, hmetric, _⟩ := hinput d H p hp hd hH
  have hshift := Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := C₁) (D := C) hp (by omega) (by dsimp [C]; omega))
  have hBC := hB.trans hshift
  have hKC : (K : ℝ) ≤ Real.exp ((p + C) ^ C) :=
    (bchBoxCoordinateBound_le_bchBoxMetricConstant s d H ⟨B, Real.exp_nonneg _⟩).trans
      (hmetric.trans hshift)
  have hhalf := (half_radius_inverse_power_bound Cᵣ hCᵣ hr hp hri).trans
    (Real.exp_le_exp.mpr (shifted_power_self_mono (C := Cᵣ + 3) (D := C)
      hp (by omega) (by dsimp [C]; omega)))
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    boxCoverCount_le_exp C d hC K (Real.exp_nonneg _) (by linarith) hp hd hBC hKC hhalf

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_realification_finite_atlas_exp_bound (s : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ),
      0 < l → scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ →
      bchSubgroupCoordinates e Γ ⊆ denominatorGrid l →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      let G := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
      let ΓR : Subgroup G := Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ centers : Fin n → G, ∃ φ : Fin n → OpenPartialHomeomorph (ι → ℝ) (G ⧸ ΓR),
          (∀ j i, |(e.baseChange ℝ).repr (centers j).coord i| ≤ Real.exp ((p + D) ^ D)) ∧
          (∀ j v, φ j v = (QuotientGroup.mk
            (centers j * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v) : G ⧸ ΓR)) ∧
          (∀ j, (φ j).source = {v | ∀ i, |v i| < r}) ∧
          (∀ x : G ⧸ ΓR, ∃ j, x ∈ (φ j).target) := by
  obtain ⟨C₀, hC₀, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨D, hD, hbudget⟩ := exists_bch_chart_cover_exp_bound s C₀ hC₀
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl hinner houter hc hp hd hH hlp
  let ΓR := Γ.map NilpotentLieBCHGroup.realificationHom
  have hgrid := NilpotentLieBCHGroup.realification_subgroup_grid e Γ l houter
  have hstructure := fun i j k => (realLieBasis_structure e i j k).symm
  let B := Real.exp ((p + C₀) ^ C₀)
  have hB : 1 ≤ B := Real.one_le_exp (by positivity)
  obtain ⟨hn, hBbound, hrbound⟩ := hbudget (Fintype.card ι) H l p hp hd hH hlp
  obtain ⟨centers, hcenters, hcover⟩ :=
    NilpotentLieBCHGroup.finite_quotient_coordinate_chart_cover
      (e.baseChange ℝ) (lieStructureConstants e) hstructure hc ΓR l hl hgrid B hB
      (hrep e hnil Γ l H p hl hinner hc hp hd hH hlp)
  refine ⟨bchInjectivityRadius s (Fintype.card ι) H l,
    bchInjectivityRadius_pos _ _ _ _, bchInjectivityRadius_le_one _ _ _ _, hrbound,
    _, by positivity, hn, centers,
    (fun j => NilpotentLieBCHGroup.quotientCoordinateChart (e.baseChange ℝ) (lieStructureConstants e)
      hstructure hc ΓR l hl hgrid (centers j)), ?_, ?_, ?_, hcover⟩
  · exact fun j i => (hcenters j i).trans hBbound
  · exact fun j => NilpotentLieBCHGroup.quotientCoordinateChart_apply _ _ _ _ _ _ _ _ (centers j)
  · exact fun j => NilpotentLieBCHGroup.quotientCoordinateChart_source _ _ _ _ _ _ _ _ (centers j)

end Erdos3

end

end OAI
