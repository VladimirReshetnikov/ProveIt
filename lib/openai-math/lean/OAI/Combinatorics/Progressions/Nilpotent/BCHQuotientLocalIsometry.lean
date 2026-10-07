import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Covering.Quotient
import OAI.Combinatorics.Progressions.Estimates.GroupReductionFactors
import OAI.Combinatorics.Progressions.Estimates.SeparatedCosetBalls
import OAI.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

section Topology

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_compact_realification_representatives (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) :
    ∃ C : Set G, IsCompact C ∧
      ∀ g : G, ∃ c ∈ C, ∃ γ ∈ Γ.map NilpotentLieBCHGroup.realificationHom, g = c * γ := by
  let : FiniteDimensional ℝ E := (e.baseChange ℝ).finiteDimensional_of_finite
  let H : ℕ → Subgroup G := fun n => NilpotentLieBCHGroup.subgroup
    (show LieIdeal ℚ E from LieModule.lowerCentralSeries ℚ E E n).toLieSubalgebra
  have hzero : H 0 = ⊤ := by
    ext g
    change (g.coord ∈ LieModule.lowerCentralSeries ℚ E E 0) ↔ g ∈ (⊤ : Subgroup G)
    simp
  have hterminal : H s = ⊥ := by
    ext g
    change (g.coord ∈ LieModule.lowerCentralSeries ℚ E E s) ↔ g = 1
    rw [realification_lowerCentralSeries_eq_bot hnil, LieSubmodule.mem_bot]
    exact ⟨fun h => NilpotentLieBCHGroup.ext h, fun h => congrArg NilpotentLieBCHGroup.coord h⟩
  apply exists_compact_representatives_of_reductions (Γ.map NilpotentLieBCHGroup.realificationHom)
    H s hzero hterminal
  intro i _
  obtain ⟨K, hK, hreduce⟩ := exists_realification_layer_reduction e Γ l hl hinner i
  exact ⟨K, hK, fun g hg => hreduce g hg⟩

theorem compactSpace_realification_quotient (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) :
    CompactSpace (G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) := by
  obtain ⟨C, hC, hrep⟩ := exists_compact_realification_representatives e Γ l hl hinner
  exact compactSpace_quotient_of_representatives _ hC hrep

end Topology

theorem exists_realification_cocompact_lattice (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ τ : TopologicalSpace E,
      letI := τ
      IsTopologicalAddGroup E ∧ ContinuousSMul ℝ E ∧ T2Space E ∧
      IsTopologicalGroup G ∧ ConnectedSpace G ∧ SimplyConnectedSpace G ∧
      IsClosed (Γ.map NilpotentLieBCHGroup.realificationHom : Set G) ∧
      IsDiscrete (Γ.map NilpotentLieBCHGroup.realificationHom : Set G) ∧
      CompactSpace (G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) := by
  obtain ⟨τ, hA, hS, hT, hG, hC, hSC, hclosed, hdiscrete⟩ :=
    exists_realification_topology_of_grid e Γ l hl houter
  let : TopologicalSpace E := τ
  let : IsTopologicalAddGroup E := hA
  let : ContinuousSMul ℝ E := hS
  let : T2Space E := hT
  exact ⟨τ, hA, hS, hT, hG, hC, hSC, hclosed, hdiscrete,
    compactSpace_realification_quotient e Γ l hl hinner⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

section Topology

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem isCoveringMap_realification_quotient (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    IsCoveringMap (QuotientGroup.mk : G → G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) := by
  let : FiniteDimensional ℝ E := (e.baseChange ℝ).finiteDimensional_of_finite
  exact ((Γ.map NilpotentLieBCHGroup.realificationHom).isQuotientCoveringMap
    (NilpotentLieBCHGroup.realification_subgroup_closed_discrete e Γ l hl houter).2).isCoveringMap

end Topology

theorem exists_realification_lieGroup_lattice (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ τ : TopologicalSpace E,
      letI := τ
      ∃ c : ChartedSpace (ι → ℝ) G,
        letI := c
        IsTopologicalAddGroup E ∧ ContinuousSMul ℝ E ∧ T2Space E ∧
        LieGroup 𝓘(ℝ, ι → ℝ) ω G ∧ IsTopologicalGroup G ∧
        ConnectedSpace G ∧ SimplyConnectedSpace G ∧ SecondCountableTopology G ∧
        Group.IsNilpotent G ∧ Group.nilpotencyClass G ≤ s ∧
        IsClosed (Γ.map NilpotentLieBCHGroup.realificationHom : Set G) ∧
        IsDiscrete (Γ.map NilpotentLieBCHGroup.realificationHom : Set G) ∧
        CompactSpace (G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) ∧
        IsCoveringMap (QuotientGroup.mk : G → G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) := by
  obtain ⟨τ, hA, hS, hT, hG, hC, hSC, hclosed, hdiscrete, hcompact⟩ :=
    exists_realification_cocompact_lattice e Γ l hl hinner houter
  let : TopologicalSpace E := τ
  let : IsTopologicalAddGroup E := hA
  let : ContinuousSMul ℝ E := hS
  let : T2Space E := hT
  refine ⟨τ, NilpotentLieBCHGroup.basisChartedSpace (e.baseChange ℝ),
    hA, hS, hT, NilpotentLieBCHGroup.lieGroup_basis (e.baseChange ℝ) ω,
    hG, hC, hSC, ?_, NilpotentLieBCHGroup.isNilpotentGroup,
    NilpotentLieBCHGroup.nilpotencyClass_le, hclosed, hdiscrete, hcompact, ?_⟩
  · exact (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).secondCountableTopology
  · exact isCoveringMap_realification_quotient e Γ l hl houter

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Set

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[instance_reducible]
noncomputable def quotientMetricSpace (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) :
    MetricSpace (NilpotentLieBCHGroup L s hnil ⧸ Γ) := by
  letI : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  letI := rightMetricSpace (hnil := hnil) e
  letI := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact rightCosetMetricSpace Γ hΓ

theorem quotientMetricSpace_topology (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) :
    (quotientMetricSpace e Γ hΓ).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (NilpotentLieBCHGroup L s hnil ⧸ Γ)) := rfl

theorem quotientMetricSpace_edist_mk (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (x y : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := quotientMetricSpace e Γ hΓ
    edist (QuotientGroup.mk x : _ ⧸ Γ) (QuotientGroup.mk y) = ⨅ γ : Γ, edist x (y * γ) := rfl

theorem quotientMetricSpace_lipschitz_mk (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := quotientMetricSpace e Γ hΓ
    LipschitzWith 1 (QuotientGroup.mk : NilpotentLieBCHGroup L s hnil → _ ⧸ Γ) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact rightCosetMetricSpace_lipschitz_mk Γ hΓ

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

local notation "G" => NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)

@[instance_reducible]
noncomputable def realificationQuotientMetricSpace (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    MetricSpace (G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) :=
  NilpotentLieBCHGroup.quotientMetricSpace (e.baseChange ℝ)
    (Γ.map NilpotentLieBCHGroup.realificationHom)
    (NilpotentLieBCHGroup.realification_subgroup_closed_discrete e Γ l hl houter).1

theorem realificationQuotientMetricSpace_topology (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    (realificationQuotientMetricSpace e Γ l hl houter).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom)) := rfl

theorem realificationQuotientMetricSpace_compact (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    letI := realificationQuotientMetricSpace e Γ l hl houter
    CompactSpace (G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) :=
  compactSpace_realification_quotient e Γ l hl hinner

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

noncomputable def realificationLieHom (φ : L →ₗ⁅ℚ⁆ M) :
    (ℝ ⊗[ℚ] L) →ₗ⁅ℝ⁆ (ℝ ⊗[ℚ] M) where
  toLinearMap := φ.toLinearMap.baseChange ℝ
  map_lie' {x y} := (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) φ).map_lie x y

@[simp] theorem realificationLieHom_tmul (φ : L →ₗ⁅ℚ⁆ M) (a : ℝ) (x : L) :
    realificationLieHom φ (a ⊗ₜ[ℚ] x) = a ⊗ₜ[ℚ] φ x := rfl

theorem realificationLieHom_inclusion (φ : L →ₗ⁅ℚ⁆ M) (x : L) :
    realificationLieHom φ (rationalLieInclusion x) = rationalLieInclusion (φ x) := rfl

theorem realificationLieHom_basis (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (k : κ) (i : ι) :
    (f.baseChange ℝ).repr (realificationLieHom φ ((e.baseChange ℝ) i)) k =
      (f.repr (φ (e i)) k : ℝ) := by
  simp only [Basis.baseChange_apply, realificationLieHom_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

namespace NilpotentLieBCHGroup

variable {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

noncomputable def realificationMap (φ : L →ₗ⁅ℚ⁆ M) :
    NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) →*
      NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM) :=
  mapReal (realificationLieHom φ)

@[simp] theorem realificationMap_coord (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    (realificationMap (hnil := hnil) (hM := hM) φ g).coord = realificationLieHom φ g.coord := rfl

theorem realificationMap_realificationHom_ofSteps (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup L s hnil) :
    realificationMap (hnil := hnil) (hM := hM) φ (realificationHom g) =
      realificationHom (mapOfSteps (hM := hM) φ g) := by
  apply ext
  rfl

theorem realificationMap_realificationHom
    {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}
    (φ : L →ₗ⁅ℚ⁆ M) (g : NilpotentLieBCHGroup L s hnil) :
    realificationMap (hnil := hnil) (hM := hM) φ (realificationHom g) =
      realificationHom (map (hM := hM) φ g) := by
  apply ext
  rfl

theorem realificationMap_subgroup (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (Λ : Subgroup (NilpotentLieBCHGroup M t hM)) (hφ : Γ ≤ Λ.comap (mapOfSteps φ)) :
    Γ.map realificationHom ≤ (Λ.map realificationHom).comap
      (realificationMap (hnil := hnil) (hM := hM) φ) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  change realificationMap (hnil := hnil) (hM := hM) φ (realificationHom y) ∈ Λ.map realificationHom
  rw [realificationMap_realificationHom_ofSteps (hM := hM)]
  exact Subgroup.mem_map.mpr ⟨mapOfSteps φ y, hφ hy, rfl⟩

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

def coordinateLipschitzBound (m n : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  ((m : ℝ≥0) + n + 1) * (B + 1)

theorem coordinateLipschitzBound_pos (m n : ℕ) (B : ℝ≥0) :
    0 < coordinateLipschitzBound m n B := by
  unfold coordinateLipschitzBound
  positivity

theorem coordinateLipschitzBound_le_exp (m n : ℕ) (B : ℝ≥0) {p : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hn : (n : ℝ) ≤ p)
    (hB : (B : ℝ) ≤ Real.exp p) :
    (coordinateLipschitzBound m n B : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
  have hdim : (m : ℝ) + n + 1 ≤ Real.exp (2 * p) := by
    linarith [Real.add_one_le_exp (2 * p)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hheight : (B : ℝ) + 1 ≤ Real.exp (p + 1) := by
    calc
      _ ≤ Real.exp p * 2 := by linarith [Real.one_le_exp_iff.mpr hp]
      _ ≤ Real.exp p * Real.exp 1 := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
      _ = Real.exp (p + 1) := (Real.exp_add _ _).symm
  change ((m : ℝ) + n + 1) * ((B : ℝ) + 1) ≤ _
  calc
    _ ≤ Real.exp (2 * p) * Real.exp (p + 1) :=
      mul_le_mul hdim hheight (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (3 * p + 1) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((p + 2) ^ 2) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])

namespace NilpotentLieBCHGroup

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M) (φ : L →ₗ⁅ℝ⁆ M)

theorem lipschitz_mapReal_of_entry_bound (B : ℝ≥0)
    (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B)
      (mapReal (hnil := hnil) (hM := hM) φ) := by
  apply lipschitz_mapReal_of_coordinate_bound e f φ (coordinateLipschitzBound_pos _ _ _)
  intro w
  exact basisCoordinateMap_L2_bound e f φ.toLinearMap B B.coe_nonneg hφ w

theorem lipschitz_mapReal_of_rational_height (A : κ → ι → ℚ) (H : ℕ)
    (hA : ∀ k i, f.repr (φ (e i)) k = (A k i : ℝ))
    (hH : ∀ k i, RationalHeightLE (A k i) H) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H)
      (mapReal (hnil := hnil) (hM := hM) φ) := by
  apply lipschitz_mapReal_of_entry_bound e f φ H
  intro k i
  rw [hA]
  exact (hH k i).abs_real_le

theorem exists_mapReal_lipschitz_exp_bound (B : ℝ≥0) {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hB : (B : ℝ) ≤ Real.exp p) (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := rightMetricSpace (hnil := hM) f
    ∃ C : ℝ≥0, 0 < C ∧ (C : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
      LipschitzWith C (mapReal (hnil := hnil) (hM := hM) φ) := by
  exact ⟨coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B,
    coordinateLipschitzBound_pos _ _ _, coordinateLipschitzBound_le_exp _ _ B hp hκ hι hB,
    lipschitz_mapReal_of_entry_bound e f φ B hφ⟩

variable (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (Λ : Subgroup (NilpotentLieBCHGroup M t hM))
  (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
  (hΛ : IsClosed (Λ : Set (NilpotentLieBCHGroup M t hM)))
  (hmap : Γ ≤ Λ.comap (mapReal φ))

theorem lipschitz_quotient_mapReal_of_entry_bound (B : ℝ≥0)
    (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B) :
    letI := quotientMetricSpace e Γ hΓ
    letI := quotientMetricSpace f Λ hΛ
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B)
      (cosetMap Γ Λ (mapReal φ) hmap) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let : FiniteDimensional ℝ M := f.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hM) f
  exact lipschitz_cosetMap Γ Λ hΓ hΛ (mapReal φ) hmap
    (lipschitz_mapReal_of_entry_bound e f φ B hφ)

theorem exists_quotient_mapReal_lipschitz_exp_bound (B : ℝ≥0) {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hB : (B : ℝ) ≤ Real.exp p) (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B) :
    letI := quotientMetricSpace e Γ hΓ
    letI := quotientMetricSpace f Λ hΛ
    ∃ C : ℝ≥0, 0 < C ∧ (C : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
      LipschitzWith C (cosetMap Γ Λ (mapReal φ) hmap) := by
  exact ⟨coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B,
    coordinateLipschitzBound_pos _ _ _, coordinateLipschitzBound_le_exp _ _ B hp hκ hι hB,
    lipschitz_quotient_mapReal_of_entry_bound e f φ Γ Λ hΓ hΛ hmap B hφ⟩

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

section Distance

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def basisRiemannianDist (e : Basis ι ℝ L) (x y : NilpotentLieBCHGroup L s hnil) : ℝ :=
  letI := rightMetricSpace (hnil := hnil) e
  dist x y

noncomputable def basisQuotientDist (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) (x y : _ ⧸ Γ) : ℝ :=
  letI := quotientMetricSpace e Γ hΓ
  dist x y

end Distance

section Map

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem basisRiemannianDist_mapReal_le (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ⁅ℝ⁆ M) (B : ℝ≥0) (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B)
    (x y : NilpotentLieBCHGroup L s hnil) :
    basisRiemannianDist f (mapReal (hM := hM) φ x) (mapReal (hM := hM) φ y) ≤
      coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B * basisRiemannianDist e x y := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace (hnil := hM) f
  exact (lipschitz_mapReal_of_entry_bound e f φ B hφ).dist_le_mul x y

theorem basisQuotientDist_mapReal_le (e : Basis ι ℝ L) (f : Basis κ ℝ M)
    (φ : L →ₗ⁅ℝ⁆ M) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (Λ : Subgroup (NilpotentLieBCHGroup M s hM))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (hΛ : IsClosed (Λ : Set (NilpotentLieBCHGroup M s hM)))
    (hmap : Γ ≤ Λ.comap (mapReal φ)) (B : ℝ≥0) (hφ : ∀ k i, |f.repr (φ (e i)) k| ≤ B)
    (x y : _ ⧸ Γ) :
    basisQuotientDist f Λ hΛ (cosetMap Γ Λ (mapReal φ) hmap x) (cosetMap Γ Λ (mapReal φ) hmap y) ≤
      coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B * basisQuotientDist e Γ hΓ x y := by
  let := quotientMetricSpace e Γ hΓ
  let := quotientMetricSpace f Λ hΛ
  exact (lipschitz_quotient_mapReal_of_entry_bound e f φ Γ Λ hΓ hΛ hmap B hφ).dist_le_mul x y

end Map

section BasisChange

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

omit [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] in
@[simp] theorem mapReal_id (x : NilpotentLieBCHGroup L s hnil) :
    mapReal (hM := hnil) (LieHom.id : L →ₗ⁅ℝ⁆ L) x = x := rfl

theorem basisRiemannianDist_change_le (e : Basis ι ℝ L) (f : Basis κ ℝ L)
    (B : ℝ≥0) (hB : ∀ k i, |f.repr (e i) k| ≤ B) (x y : NilpotentLieBCHGroup L s hnil) :
    basisRiemannianDist f x y ≤
      coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B * basisRiemannianDist e x y := by
  simpa only [mapReal_id] using
    basisRiemannianDist_mapReal_le (hM := hnil) e f LieHom.id B hB x y

theorem basisRiemannianDist_compare (e : Basis ι ℝ L) (f : Basis κ ℝ L)
    (B D : ℝ≥0) (hB : ∀ k i, |f.repr (e i) k| ≤ B) (hD : ∀ i k, |e.repr (f k) i| ≤ D)
    (x y : NilpotentLieBCHGroup L s hnil) :
    basisRiemannianDist f x y ≤
        coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B * basisRiemannianDist e x y ∧
      basisRiemannianDist e x y ≤
        coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) D * basisRiemannianDist f x y :=
  ⟨basisRiemannianDist_change_le e f B hB x y, basisRiemannianDist_change_le f e D hD x y⟩

theorem basisRiemannianDist_exp_change_le (e : Basis ι ℝ L) (f : Basis κ ℝ L)
    (B : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hBp : (B : ℝ) ≤ Real.exp p) (hB : ∀ k i, |f.repr (e i) k| ≤ B)
    (x y : NilpotentLieBCHGroup L s hnil) :
    basisRiemannianDist f x y ≤ Real.exp ((p + 2) ^ 2) * basisRiemannianDist e x y := by
  let := rightMetricSpace (hnil := hnil) e
  have hn : 0 ≤ basisRiemannianDist e x y := dist_nonneg
  exact (basisRiemannianDist_change_le e f B hB x y).trans
    (mul_le_mul_of_nonneg_right (coordinateLipschitzBound_le_exp _ _ B hp hκ hι hBp) hn)

theorem basisRiemannianDist_exp_compare (e : Basis ι ℝ L) (f : Basis κ ℝ L)
    (B : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hBp : (B : ℝ) ≤ Real.exp p)
    (hB : ∀ k i, |f.repr (e i) k| ≤ B) (hD : ∀ i k, |e.repr (f k) i| ≤ B)
    (x y : NilpotentLieBCHGroup L s hnil) :
    basisRiemannianDist f x y ≤ Real.exp ((p + 2) ^ 2) * basisRiemannianDist e x y ∧
      basisRiemannianDist e x y ≤ Real.exp ((p + 2) ^ 2) * basisRiemannianDist f x y :=
  ⟨basisRiemannianDist_exp_change_le e f B hp hι hκ hBp hB x y,
    basisRiemannianDist_exp_change_le f e B hp hκ hι hBp hD x y⟩

theorem basisQuotientDist_change_le (e : Basis ι ℝ L) (f : Basis κ ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (B : ℝ≥0) (hB : ∀ k i, |f.repr (e i) k| ≤ B) (x y : _ ⧸ Γ) :
    basisQuotientDist f Γ hΓ x y ≤
      coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B * basisQuotientDist e Γ hΓ x y := by
  have hmap : Γ ≤ Γ.comap (mapReal (LieHom.id : L →ₗ⁅ℝ⁆ L)) := by
    intro g hg
    simpa only [Subgroup.mem_comap, mapReal_id] using hg
  have heq : cosetMap Γ Γ (mapReal (LieHom.id : L →ₗ⁅ℝ⁆ L)) hmap = id := by
    funext z
    induction z using Quotient.inductionOn with
    | h z => rfl
  simpa only [heq, id_eq] using
    basisQuotientDist_mapReal_le e f LieHom.id Γ Γ hΓ hΓ hmap B hB x y

theorem basisQuotientDist_compare (e : Basis ι ℝ L) (f : Basis κ ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (B D : ℝ≥0) (hB : ∀ k i, |f.repr (e i) k| ≤ B) (hD : ∀ i k, |e.repr (f k) i| ≤ D)
    (x y : _ ⧸ Γ) :
    basisQuotientDist f Γ hΓ x y ≤
        coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) B * basisQuotientDist e Γ hΓ x y ∧
      basisQuotientDist e Γ hΓ x y ≤
        coordinateLipschitzBound (Fintype.card ι) (Fintype.card κ) D * basisQuotientDist f Γ hΓ x y :=
  ⟨basisQuotientDist_change_le e f Γ hΓ B hB x y,
    basisQuotientDist_change_le f e Γ hΓ D hD x y⟩

theorem basisQuotientDist_exp_change_le (e : Basis ι ℝ L) (f : Basis κ ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (B : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hBp : (B : ℝ) ≤ Real.exp p) (hB : ∀ k i, |f.repr (e i) k| ≤ B) (x y : _ ⧸ Γ) :
    basisQuotientDist f Γ hΓ x y ≤ Real.exp ((p + 2) ^ 2) * basisQuotientDist e Γ hΓ x y := by
  let := quotientMetricSpace e Γ hΓ
  have hn : 0 ≤ basisQuotientDist e Γ hΓ x y := dist_nonneg
  exact (basisQuotientDist_change_le e f Γ hΓ B hB x y).trans
    (mul_le_mul_of_nonneg_right (coordinateLipschitzBound_le_exp _ _ B hp hκ hι hBp) hn)

theorem basisQuotientDist_exp_compare (e : Basis ι ℝ L) (f : Basis κ ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (B : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hBp : (B : ℝ) ≤ Real.exp p)
    (hB : ∀ k i, |f.repr (e i) k| ≤ B) (hD : ∀ i k, |e.repr (f k) i| ≤ B) (x y : _ ⧸ Γ) :
    basisQuotientDist f Γ hΓ x y ≤ Real.exp ((p + 2) ^ 2) * basisQuotientDist e Γ hΓ x y ∧
      basisQuotientDist e Γ hΓ x y ≤ Real.exp ((p + 2) ^ 2) * basisQuotientDist f Γ hΓ x y :=
  ⟨basisQuotientDist_exp_change_le e f Γ hΓ B hp hι hκ hBp hB x y,
    basisQuotientDist_exp_change_le f e Γ hΓ B hp hκ hι hBp hD x y⟩

end BasisChange

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (a : NilpotentLieBCHGroup L s hnil)

theorem lipschitz_conjugation_of_basis_bound (B : ℝ≥0)
    (hB : ∀ i k, |e.repr (a * (⟨e i⟩ : NilpotentLieBCHGroup L s hnil) * a⁻¹).coord k| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    LipschitzWith (coordinateLipschitzBound (Fintype.card ι) (Fintype.card ι) B)
      (MulAut.conj a) := by
  classical
  apply lipschitz_linear_hom e e (MulAut.conj a).toMonoidHom (conjugationLinearMap e a)
    (homCoordinates_conjugation_eq e a) (coordinateLipschitzBound_pos _ _ _)
  intro v
  apply coordinateLinearMap_L2_bound _ B B.coe_nonneg
  intro k i
  rw [conjugationLinearMap_basis]
  exact hB i k

theorem lipschitz_mul_left_of_basis_bound (B : ℝ≥0)
    (hB : ∀ i k, |e.repr (a * (⟨e i⟩ : NilpotentLieBCHGroup L s hnil) * a⁻¹).coord k| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    LipschitzWith (coordinateLipschitzBound (Fintype.card ι) (Fintype.card ι) B)
      (fun x => a * x) := by
  let := rightMetricSpace (hnil := hnil) e
  have h := (rightMetricSpace_isometry_mul_right e a).lipschitzWith.comp
    (lipschitz_conjugation_of_basis_bound e a B hB)
  simpa only [one_mul, Function.comp_def, MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using h

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct NNReal

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
  {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

variable (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)

theorem lipschitz_realificationMap (H : ℕ)
    (hH : ∀ k i, RationalHeightLE (f.repr (φ (e i)) k) H) :
    letI := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ)
    letI := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H)
      (realificationMap (hnil := hnil) (hM := hM) φ) :=
  lipschitz_mapReal_of_rational_height (e.baseChange ℝ) (f.baseChange ℝ) (realificationLieHom φ)
    (fun k i => f.repr (φ (e i)) k) H (realificationLieHom_basis e f φ) hH

theorem exists_realificationMap_lipschitz_exp_bound (H : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hH : ∀ k i, RationalHeightLE (f.repr (φ (e i)) k) H) :
    letI := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hnil) (e.baseChange ℝ)
    letI := rightMetricSpace (hnil := realification_lowerCentralSeries_eq_bot hM) (f.baseChange ℝ)
    ∃ C : ℝ≥0, 0 < C ∧ (C : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
      LipschitzWith C (realificationMap (hnil := hnil) (hM := hM) φ) :=
  ⟨coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H,
    coordinateLipschitzBound_pos _ _ _, coordinateLipschitzBound_le_exp _ _ H hp hκ hι hHp,
    lipschitz_realificationMap e f φ H hH⟩

variable (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (Λ : Subgroup (NilpotentLieBCHGroup M t hM)) (hφ : Γ ≤ Λ.comap (mapOfSteps φ))

theorem lipschitz_realificationMap_quotient (l m : ℕ) (hl : 0 < l) (hm : 0 < m)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hΛ : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m)
    (H : ℕ) (hH : ∀ k i, RationalHeightLE (f.repr (φ (e i)) k) H) :
    letI := realificationQuotientMetricSpace e Γ l hl hΓ
    letI := realificationQuotientMetricSpace f Λ m hm hΛ
    LipschitzWith (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H)
      (cosetMap (Γ.map realificationHom) (Λ.map realificationHom)
        (realificationMap (hnil := hnil) (hM := hM) φ)
        (realificationMap_subgroup φ Γ Λ hφ)) := by
  apply lipschitz_quotient_mapReal_of_entry_bound (e.baseChange ℝ) (f.baseChange ℝ)
    (realificationLieHom φ) (Γ.map realificationHom) (Λ.map realificationHom)
    (realification_subgroup_closed_discrete e Γ l hl hΓ).1
    (realification_subgroup_closed_discrete f Λ m hm hΛ).1
    (realificationMap_subgroup φ Γ Λ hφ) H
  intro k i
  rw [realificationLieHom_basis]
  exact (hH k i).abs_real_le

theorem exists_realificationMap_quotient_lipschitz_exp_bound
    (l m : ℕ) (hl : 0 < l) (hm : 0 < m)
    (hΓ : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    (hΛ : bchSubgroupCoordinates f Λ ⊆ denominatorGrid m)
    (H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hH : ∀ k i, RationalHeightLE (f.repr (φ (e i)) k) H) :
    letI := realificationQuotientMetricSpace e Γ l hl hΓ
    letI := realificationQuotientMetricSpace f Λ m hm hΛ
    ∃ C : ℝ≥0, 0 < C ∧ (C : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
      LipschitzWith C (cosetMap (Γ.map realificationHom) (Λ.map realificationHom)
        (realificationMap (hnil := hnil) (hM := hM) φ) (realificationMap_subgroup φ Γ Λ hφ)) :=
  ⟨coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι) H,
    coordinateLipschitzBound_pos _ _ _, coordinateLipschitzBound_le_exp _ _ H hp hκ hι hHp,
    lipschitz_realificationMap_quotient e f φ Γ Λ hφ l m hl hm hΓ hΛ H hH⟩

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

theorem quotient_dist_eq_on_ball_of_lattice_grid
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l) :
    letI := rightMetricSpace (hnil := hnil) e
    ∀ (C : ℝ≥0), 0 < C → ∀ z : NilpotentLieBCHGroup L s hnil,
      LipschitzWith C (fun x => z⁻¹ * x) →
      letI := quotientMetricSpace e Γ hΓ
      ∀ {x y : NilpotentLieBCHGroup L s hnil},
        dist x z ≤ bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * C) →
        dist y z ≤ bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * C) →
        dist (QuotientGroup.mk x : _ ⧸ Γ) (QuotientGroup.mk y) = dist x y := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  intro C hC z hleft
  have hC' : (0 : ℝ) < C := hC
  have hgap := fun γ hγ hne => latticeSeparationRadius_le_dist e c hstructure hc Γ l hl hgrid γ hγ hne
  apply quotient_dist_eq_of_separated_ball Γ hΓ z _
  apply separated_ball_of_lipschitz_left Γ hC hgap ?_ z hleft
  have heq : 4 * (bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * (C : ℝ))) * C =
      bchLatticeSeparationRadius s (Fintype.card ι) H l := by
    field_simp
  exact heq.le

end Erdos3.NilpotentLieBCHGroup

end

end OAI
