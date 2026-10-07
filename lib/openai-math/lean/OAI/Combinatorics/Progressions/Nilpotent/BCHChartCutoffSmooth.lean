/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ModuleTopology
import OAI.Combinatorics.Progressions.Estimates.RightCosetEDistance
import OAI.Combinatorics.Progressions.Geometry.LieCoordinateSmooth
import OAI.Combinatorics.Progressions.Linear.RationalSpanCoordinates

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥} [TopologicalSpace L]

instance : TopologicalSpace (NilpotentLieBCHGroup L s hnil) :=
  TopologicalSpace.induced coord inferInstance

@[fun_prop]
theorem continuous_coord : Continuous (coord : NilpotentLieBCHGroup L s hnil → L) :=
  continuous_induced_dom

@[fun_prop]
theorem continuous_mk : Continuous (fun x : L => (⟨x⟩ : NilpotentLieBCHGroup L s hnil)) :=
  continuous_induced_rng.mpr continuous_id

def coordHomeomorph : NilpotentLieBCHGroup L s hnil ≃ₜ L where
  toFun := coord
  invFun x := ⟨x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_coord
  continuous_invFun := continuous_mk

instance [T2Space L] : T2Space (NilpotentLieBCHGroup L s hnil) :=
  (coordHomeomorph (hnil := hnil)).isEmbedding.t2Space

instance [ContractibleSpace L] : ContractibleSpace (NilpotentLieBCHGroup L s hnil) :=
  (coordHomeomorph (hnil := hnil)).contractibleSpace

theorem isTopologicalGroup_of_continuous_lie [IsTopologicalAddGroup L] [ContinuousConstSMul ℚ L]
    (hlie : Continuous (fun z : L × L => ⁅z.1, z.2⁆)) :
    IsTopologicalGroup (NilpotentLieBCHGroup L s hnil) where
  continuous_mul := by
    change Continuous (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
      (⟨lieBCH s z.1.coord z.2.coord⟩ : NilpotentLieBCHGroup L s hnil))
    have hcoords : Continuous
        (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          (z.1.coord, z.2.coord)) :=
      (continuous_coord.comp continuous_fst).prodMk (continuous_coord.comp continuous_snd)
    have hbch : Continuous
        (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          lieBCH s z.1.coord z.2.coord) :=
      Continuous.comp
        (g := fun z : L × L => lieBCH s z.1 z.2)
        (f := fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          (z.1.coord, z.2.coord))
        (continuous_lieBCH (L := L) hlie s) hcoords
    exact (continuous_mk (hnil := hnil)).comp hbch
  continuous_inv := by
    change Continuous (fun z : NilpotentLieBCHGroup L s hnil =>
      (⟨-z.coord⟩ : NilpotentLieBCHGroup L s hnil))
    exact (continuous_mk (hnil := hnil)).comp (continuous_coord (hnil := hnil)).neg

theorem continuous_map_of_continuous {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace M] {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : Continuous φ) :
    Continuous (map (hnil := hnil) (hM := hM) φ) :=
  continuous_mk.comp (hφ.comp continuous_coord)

section Real

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L]

instance : IsTopologicalGroup (NilpotentLieBCHGroup L s hnil) := by
  let : ContinuousConstSMul ℚ L := ⟨fun q => by
    simpa only [algebraMap_smul] using
      (continuous_const_smul (algebraMap ℚ ℝ q) : Continuous (fun x : L => algebraMap ℚ ℝ q • x))⟩
  exact isTopologicalGroup_of_continuous_lie continuous_lie_finiteDimensional

omit [IsScalarTower ℚ ℝ L] [T2Space L] [FiniteDimensional ℝ L] in

theorem connected_simplyConnected :
    ConnectedSpace (NilpotentLieBCHGroup L s hnil) ∧
      SimplyConnectedSpace (NilpotentLieBCHGroup L s hnil) := by
  constructor <;> infer_instance

end Real

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def basisHomeomorph (e : Basis ι ℝ L) :
    NilpotentLieBCHGroup L s hnil ≃ₜ (ι → ℝ) :=
  (coordHomeomorph (hnil := hnil)).trans e.equivFunL.toHomeomorph

@[simp]
theorem basisHomeomorph_apply (e : Basis ι ℝ L) (g : NilpotentLieBCHGroup L s hnil) :
    basisHomeomorph e g = e.equivFun g.coord := rfl

theorem closed_discrete_subgroup_of_grid (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l) :
    IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)) ∧
      IsDiscrete (Γ : Set (NilpotentLieBCHGroup L s hnil)) := by
  let f := basisHomeomorph (hnil := hnil) e
  have hsub : (Γ : Set (NilpotentLieBCHGroup L s hnil)) ⊆ f ⁻¹' realDenominatorGrid l :=
    fun g hg => hgrid g hg
  have hd : IsDiscrete (f ⁻¹' realDenominatorGrid l) :=
    (isDiscrete_realDenominatorGrid l hl).preimage f.continuous.continuousOn f.injective
  have hc : IsClosed (f ⁻¹' realDenominatorGrid l) :=
    (isClosed_realDenominatorGrid l).preimage f.continuous
  exact ⟨isClosed_of_subset_discrete_closed hsub hd hc, hd.mono hsub⟩

theorem discreteTopology_subgroup_of_grid (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l) :
    DiscreteTopology Γ :=
  isDiscrete_iff_discreteTopology.mp (closed_discrete_subgroup_of_grid e Γ l hl hgrid).2

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

noncomputable def realLieSubalgebraOverRat (K : LieSubalgebra ℝ L) : LieSubalgebra ℚ L :=
  { K.toSubmodule.restrictScalars ℚ with lie_mem' := K.lie_mem }

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realLieSubgroup (K : LieSubalgebra ℝ L) : Subgroup (NilpotentLieBCHGroup L s hnil) :=
  subgroup (realLieSubalgebraOverRat K)

theorem mem_realLieSubgroup (K : LieSubalgebra ℝ L) (g : NilpotentLieBCHGroup L s hnil) :
    g ∈ realLieSubgroup K ↔ g.coord ∈ K := Iff.rfl

variable [TopologicalSpace L]

def realLieSubgroupCoordHomeomorph (K : LieSubalgebra ℝ L) :
    realLieSubgroup (hnil := hnil) K ≃ₜ K.toSubmodule where
  toFun g := ⟨g.1.coord, g.2⟩
  invFun v := ⟨⟨v.1⟩, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_coord.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_mk.comp continuous_subtype_val).subtype_mk _

variable [IsTopologicalAddGroup L] [ContinuousSMul ℝ L]

theorem realLieSubgroup_contractible (K : LieSubalgebra ℝ L) :
    ContractibleSpace (realLieSubgroup (hnil := hnil) K) :=
  (realLieSubgroupCoordHomeomorph K).contractibleSpace

theorem realLieSubgroup_connected_simplyConnected (K : LieSubalgebra ℝ L) :
    ConnectedSpace (realLieSubgroup (hnil := hnil) K) ∧
      SimplyConnectedSpace (realLieSubgroup (hnil := hnil) K) := by
  let := realLieSubgroup_contractible (hnil := hnil) K
  exact ⟨inferInstance, inferInstance⟩

theorem realLieSubgroup_closed [T2Space L] [FiniteDimensional ℝ L] (K : LieSubalgebra ℝ L) :
    IsClosed (realLieSubgroup (hnil := hnil) K : Set (NilpotentLieBCHGroup L s hnil)) :=
  K.toSubmodule.closed_of_finiteDimensional.preimage continuous_coord

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def coordinateBox (e : Basis ι ℝ L) (B : ℝ) : Set (NilpotentLieBCHGroup L s hnil) :=
  {g | ∀ i, |e.repr g.coord i| ≤ B}

variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

theorem isCompact_coordinateBox (e : Basis ι ℝ L) (B : ℝ) :
    IsCompact (coordinateBox (hnil := hnil) e B) := by
  let f := basisHomeomorph (hnil := hnil) e
  have heq : coordinateBox (hnil := hnil) e B =
      f.symm '' Set.univ.pi (fun _ : ι => Set.Icc (-B) B) := by
    ext g
    constructor
    · intro hg
      refine ⟨f g, ?_, f.symm_apply_apply g⟩
      intro i _
      exact abs_le.mp (hg i)
    · rintro ⟨v, hv, rfl⟩ i
      apply abs_le.mpr
      have hi : e.repr (f.symm v).coord i = v i := congrFun (f.apply_symm_apply v) i
      rw [hi]
      exact hv i (Set.mem_univ i)
  rw [heq]
  exact (isCompact_univ_pi (fun _ : ι => isCompact_Icc)).image f.symm.continuous

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[instance_reducible]
noncomputable def basisChartedSpace (e : Basis ι ℝ L) :
    ChartedSpace (ι → ℝ) (NilpotentLieBCHGroup L s hnil) :=
  (basisHomeomorph (hnil := hnil) e).isOpenEmbedding.singletonChartedSpace

variable (e : Basis ι ℝ L)

theorem isManifold_basis (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    IsManifold 𝓘(ℝ, ι → ℝ) n (NilpotentLieBCHGroup L s hnil) :=
  (basisHomeomorph e).isOpenEmbedding.isManifold_singleton

theorem contMDiff_basisHomeomorph (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n (basisHomeomorph (hnil := hnil) e) :=
  contMDiff_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding

theorem contMDiff_basisHomeomorph_symm (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n (basisHomeomorph (hnil := hnil) e).symm := by
  let := basisChartedSpace (hnil := hnil) e
  apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding
  have heq : (basisHomeomorph (hnil := hnil) e) ∘ (basisHomeomorph e).symm = id :=
    funext (fun x => (basisHomeomorph e).apply_symm_apply x)
  rw [heq]
  exact contMDiff_id

noncomputable def basisDiffeomorph (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    (NilpotentLieBCHGroup L s hnil) ≃ₘ^n⟮𝓘(ℝ, ι → ℝ), 𝓘(ℝ, ι → ℝ)⟯ (ι → ℝ) := by
  letI := basisChartedSpace (hnil := hnil) e
  exact
    { toEquiv := (basisHomeomorph e).toEquiv
      contMDiff_toFun := contMDiff_basisHomeomorph e n
      contMDiff_invFun := contMDiff_basisHomeomorph_symm e n }

variable [IsScalarTower ℚ ℝ L]

theorem lieGroup_basis (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    LieGroup 𝓘(ℝ, ι → ℝ) n (NilpotentLieBCHGroup L s hnil) := by
  let := basisChartedSpace (hnil := hnil) e
  refine
    { __ := isManifold_basis (hnil := hnil) e n
      contMDiff_mul := ?_
      contMDiff_inv := ?_ }
  · apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding
    have hcoords : ContMDiff (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ))
        𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) n
        (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          (basisHomeomorph e z.1, basisHomeomorph e z.2)) :=
      ((contMDiff_basisHomeomorph e n).comp contMDiff_fst).prodMk_space
        ((contMDiff_basisHomeomorph e n).comp contMDiff_snd)
    have hbch := (contDiff_coordinateBCH (n := n) e s).contMDiff.comp hcoords
    convert hbch using 1; try rfl
    funext z
    simp only [Function.comp_apply, basisHomeomorph_apply, LinearEquiv.symm_apply_apply]
    rfl
  · apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding
    have hneg := (contDiff_neg (𝕜 := ℝ) (F := ι → ℝ) (n := n)).contMDiff.comp
      (contMDiff_basisHomeomorph (hnil := hnil) e n)
    have heq : (basisHomeomorph (hnil := hnil) e) ∘ (fun z => z⁻¹) =
        (fun z => -z) ∘ (basisHomeomorph e) := by
      funext z i
      change e.equivFun (-z.coord) i = -(e.equivFun z.coord i)
      simp only [map_neg, Pi.neg_apply]
    rw [heq]
    exact hneg

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

local notation "E" => ℝ ⊗[ℚ] L
local notation "G" => NilpotentLieBCHGroup E s (realification_lowerCentralSeries_eq_bot hnil)

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] in

theorem realification_layer_reduction_in_cell {κ : Type*} [Fintype κ] (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) (n : ℕ) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = (LieModule.lowerCentralSeries ℚ L L n).toSubmodule) :
    ∀ g : G, g.coord ∈ LieModule.lowerCentralSeries ℚ E E n →
      ∃ r ∈ (fun x : E => (⟨x⟩ : G)) ''
        boundedSpanCell (fun j => rationalLieInclusion (v j)) (rationalSpanGridStep e v l : ℝ),
      ∃ w ∈ Γ.map NilpotentLieBCHGroup.realificationHom,
        (r⁻¹ * g * w⁻¹).coord ∈ LieModule.lowerCentralSeries ℚ E E (n + 1) := by
  classical
  let m := rationalSpanGridStep e v l
  have hm : 0 < m := rationalSpanGridStep_pos e v l hl
  let vR : κ → E := fun j => rationalLieInclusion (v j)
  intro g hg
  have hspanreal : (LieModule.lowerCentralSeries ℚ E E n : Set E) =
      (Submodule.span ℝ (Set.range vR) : Set E) := realification_layer_eq_span n v hspan
  have hgspan : g.coord ∈ Submodule.span ℝ (Set.range vR) :=
    (Set.ext_iff.mp hspanreal g.coord).mp hg
  obtain ⟨r, hr, z, hdecomp⟩ := exists_bounded_span_remainder vR (m : ℝ)
    (by exact_mod_cast hm) g.coord hgspan
  let wQ : L := ∑ j, ((z j : ℚ) * (m : ℚ)) • v j
  have hwQ : (⟨wQ⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ := by
    have h := hinner (rationalSpanGridStep_combination e v l z)
    change (⟨e.equivFun.symm (e.equivFun wQ)⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ at h
    simpa only [LinearEquiv.symm_apply_apply] using h
  have hdecomp' : g.coord = r + rationalLieInclusion wQ := by
    change g.coord = r + rationalLieInclusion (∑ j, ((z j : ℚ) * (m : ℚ)) • v j)
    rw [rationalLieInclusion_integer_combination v z m]
    exact hdecomp
  have hrLayer : r ∈ LieModule.lowerCentralSeries ℚ E E n :=
    (Set.ext_iff.mp hspanreal r).mpr (boundedSpanCell_subset_span vR (m : ℝ) hr)
  have hwLayer : rationalLieInclusion wQ ∈ LieModule.lowerCentralSeries ℚ E E n := by
    have h := (LieModule.lowerCentralSeries ℚ E E n).sub_mem hg hrLayer
    rwa [hdecomp', add_sub_cancel_left] at h
  have hbracket : ⁅r, rationalLieInclusion wQ⁆ ∈ LieModule.lowerCentralSeries ℚ E E (n + 1) := by
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (by simp) hwLayer
  refine ⟨⟨r⟩, ⟨r, hr, rfl⟩, NilpotentLieBCHGroup.realificationHom ⟨wQ⟩,
    Subgroup.mem_map.mpr ⟨⟨wQ⟩, hwQ, rfl⟩, ?_⟩
  have hg' : g = (⟨r + rationalLieInclusion wQ⟩ : G) := NilpotentLieBCHGroup.ext hdecomp'
  rw [hg']
  exact NilpotentLieBCHGroup.additive_remainder_mem (realification_lowerCentralSeries_eq_bot hnil)
    (LieModule.lowerCentralSeries ℚ E E (n + 1)) r (rationalLieInclusion wQ) hbracket

theorem exists_realification_layer_reduction (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) (n : ℕ) :
    ∃ K : Set G, IsCompact K ∧
      ∀ g : G, g.coord ∈ LieModule.lowerCentralSeries ℚ E E n →
        ∃ r ∈ K, ∃ w ∈ Γ.map NilpotentLieBCHGroup.realificationHom,
          (r⁻¹ * g * w⁻¹).coord ∈ LieModule.lowerCentralSeries ℚ E E (n + 1) := by
  obtain ⟨d, _, v, hspan⟩ := exists_finite_layer_spanning e n
  refine ⟨(fun x : E => (⟨x⟩ : G)) ''
    boundedSpanCell (fun j => rationalLieInclusion (v j)) (rationalSpanGridStep e v l : ℝ),
    (isCompact_boundedSpanCell _ _).image NilpotentLieBCHGroup.continuous_mk, ?_⟩
  exact realification_layer_reduction_in_cell e Γ l hl hinner n v hspan

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realificationHom_coordinates (e : Basis ι ℚ L) (g : NilpotentLieBCHGroup L s hnil) :
    (e.baseChange ℝ).equivFun (realificationHom g).coord = fun i => (e.repr g.coord i : ℝ) := by
  funext i
  exact rationalLieInclusion_coordinates e g.coord i

theorem realification_subgroup_grid (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∀ g ∈ Γ.map realificationHom,
      (e.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  rw [realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
  apply hgrid
  change (⟨e.equivFun.symm (e.equivFun a.coord)⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ
  simpa only [LinearEquiv.symm_apply_apply] using ha

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem realification_subgroup_closed_discrete (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    IsClosed (Γ.map realificationHom : Set
      (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))) ∧
    IsDiscrete (Γ.map realificationHom : Set
      (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))) :=
  closed_discrete_subgroup_of_grid (e.baseChange ℝ) (Γ.map realificationHom) l hl
    (realification_subgroup_grid e Γ l hgrid)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem rational_inclusion_mem_realLayer_iff (i : ℕ) (a : L) :
    rationalLieInclusion a ∈ F.realLayer i ↔ a ∈ F.layer i :=
  one_tmul_mem_real_baseChange_iff (F.layer i) a

theorem realificationHom_mem_subgroup_iff (i : ℕ) (g : F.Group) :
    NilpotentLieBCHGroup.realificationHom g ∈ F.realification.subgroup i ↔ g ∈ F.subgroup i :=
  F.rational_inclusion_mem_realLayer_iff i g.coord

theorem realification_subgroup_eq_realLieSubgroup (i : ℕ) :
    F.realification.subgroup i = NilpotentLieBCHGroup.realLieSubgroup
      (F.realLayer i).toLieSubalgebra := rfl

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]

theorem realification_subgroup_contractible (i : ℕ) :
    ContractibleSpace (F.realification.subgroup i) :=
  NilpotentLieBCHGroup.realLieSubgroup_contractible (F.realLayer i).toLieSubalgebra

theorem realification_subgroup_connected_simplyConnected (i : ℕ) :
    ConnectedSpace (F.realification.subgroup i) ∧ SimplyConnectedSpace (F.realification.subgroup i) :=
  NilpotentLieBCHGroup.realLieSubgroup_connected_simplyConnected (F.realLayer i).toLieSubalgebra

theorem realification_subgroup_closed [T2Space (ℝ ⊗[ℚ] L)]
    [FiniteDimensional ℚ L] (i : ℕ) :
    IsClosed (F.realification.subgroup i : Set F.realification.Group) :=
  NilpotentLieBCHGroup.realLieSubgroup_closed (F.realLayer i).toLieSubalgebra

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Set Manifold
open scoped Manifold ContDiff Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem eventuallyEq_quotient_chartInverse
    (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (z : NilpotentLieBCHGroup L s hnil) (φ : OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ))
    (hφ : ∀ v, φ v = QuotientGroup.mk (z * (basisHomeomorph e).symm v))
    (g : NilpotentLieBCHGroup L s hnil) (hg : (QuotientGroup.mk g : _ ⧸ Γ) ∈ φ.target) :
    ∃ γ : Γ, (fun h : NilpotentLieBCHGroup L s hnil => φ.symm (QuotientGroup.mk h)) =ᶠ[𝓝 g]
      (fun h => basisHomeomorph e (z⁻¹ * (h * (γ : NilpotentLieBCHGroup L s hnil)))) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let v := φ.symm (QuotientGroup.mk g)
  let a := z * (basisHomeomorph e).symm v
  have ha : (QuotientGroup.mk a : _ ⧸ Γ) = QuotientGroup.mk g :=
    (hφ v).symm.trans (φ.right_inv hg)
  let γ : Γ := ⟨g⁻¹ * a, QuotientGroup.eq.mp ha.symm⟩
  have hga : g * (γ : NilpotentLieBCHGroup L s hnil) = a := by
    simp only [γ, mul_inv_cancel_left]
  let f := fun h : NilpotentLieBCHGroup L s hnil =>
    basisHomeomorph e (z⁻¹ * (h * (γ : NilpotentLieBCHGroup L s hnil)))
  have hf : Continuous f := (basisHomeomorph e).continuous.comp
    (continuous_const.mul (continuous_id.mul continuous_const))
  have hfg : f g = v := by
    dsimp only [f]
    rw [hga]
    simp only [a, inv_mul_cancel_left, Homeomorph.apply_symm_apply]
  have hnear : ∀ᶠ h in 𝓝 g, f h ∈ φ.source :=
    hf.continuousAt (φ.open_source.mem_nhds (hfg ▸ φ.map_target hg))
  refine ⟨γ, ?_⟩
  filter_upwards [hnear] with h hh
  have hφf : φ (f h) = (QuotientGroup.mk h : _ ⧸ Γ) := by
    rw [hφ]
    dsimp only [f]
    rw [Homeomorph.symm_apply_apply, mul_inv_cancel_left]
    exact quotient_mk_mul_mem Γ h γ
  change φ.symm (QuotientGroup.mk h) = f h
  rw [← hφf, φ.left_inv hh]

theorem contMDiffAt_quotient_chartInverse
    (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (z : NilpotentLieBCHGroup L s hnil) (φ : OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ))
    (hφ : ∀ v, φ v = QuotientGroup.mk (z * (basisHomeomorph e).symm v))
    (n : ℕ∞ω) (g : NilpotentLieBCHGroup L s hnil) (hg : (QuotientGroup.mk g : _ ⧸ Γ) ∈ φ.target) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiffAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n
      (fun h : NilpotentLieBCHGroup L s hnil => φ.symm (QuotientGroup.mk h)) g := by
  let := basisChartedSpace (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e n
  obtain ⟨γ, hγ⟩ := eventuallyEq_quotient_chartInverse e Γ z φ hφ g hg
  have hsmooth : ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n
      (fun h : NilpotentLieBCHGroup L s hnil =>
        basisHomeomorph e (z⁻¹ * (h * (γ : NilpotentLieBCHGroup L s hnil)))) :=
    (contMDiff_basisHomeomorph e n).comp (contMDiff_const.mul (contMDiff_id.mul contMDiff_const))
  exact hsmooth.contMDiffAt.congr_of_eventuallyEq hγ

theorem contDiffOn_quotient_chart_transition
    (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (z w : NilpotentLieBCHGroup L s hnil) (φ ψ : OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ))
    (hφ : ∀ v, φ v = QuotientGroup.mk (z * (basisHomeomorph e).symm v))
    (hψ : ∀ v, ψ v = QuotientGroup.mk (w * (basisHomeomorph e).symm v)) (n : ℕ∞ω) :
    ContDiffOn ℝ n (φ.trans ψ.symm) (φ.trans ψ.symm).source := by
  let := basisChartedSpace (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e n
  intro v hv
  have htarget : (QuotientGroup.mk (z * (basisHomeomorph e).symm v) : _ ⧸ Γ) ∈ ψ.target := by
    rw [← hφ]
    exact hv.2
  have hi := contMDiffAt_quotient_chartInverse e Γ w ψ hψ n
    (z * (basisHomeomorph e).symm v) htarget
  have hz : ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n
      (fun u : ι → ℝ => z * (basisHomeomorph e).symm u) :=
    contMDiff_const.mul (contMDiff_basisHomeomorph_symm e n)
  have ht := (hi.comp v hz.contMDiffAt).contDiffAt.contDiffWithinAt (s := (φ.trans ψ.symm).source)
  simpa only [Function.comp_def, OpenPartialHomeomorph.coe_trans, hφ] using ht

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem exists_realification_topology_of_grid (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∃ τ : TopologicalSpace (ℝ ⊗[ℚ] L),
      letI := τ
      IsTopologicalAddGroup (ℝ ⊗[ℚ] L) ∧ ContinuousSMul ℝ (ℝ ⊗[ℚ] L) ∧ T2Space (ℝ ⊗[ℚ] L) ∧
      IsTopologicalGroup (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) ∧
      ConnectedSpace (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) ∧
      SimplyConnectedSpace (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) ∧
      IsClosed (Γ.map NilpotentLieBCHGroup.realificationHom : Set
        (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))) ∧
      IsDiscrete (Γ.map NilpotentLieBCHGroup.realificationHom : Set
        (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))) := by
  let τ := moduleTopology ℝ (ℝ ⊗[ℚ] L)
  let : TopologicalSpace (ℝ ⊗[ℚ] L) := τ
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] L) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (e.baseChange ℝ).finiteDimensional_of_finite
  have hcoord : Continuous (e.baseChange ℝ).equivFun :=
    IsModuleTopology.continuous_of_linearMap (e.baseChange ℝ).equivFun.toLinearMap
  let : T2Space (ℝ ⊗[ℚ] L) :=
    T2Space.of_injective_continuous (e.baseChange ℝ).equivFun.injective hcoord
  refine ⟨τ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact NilpotentLieBCHGroup.realification_subgroup_closed_discrete e Γ l hl hgrid

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Set Manifold
open scoped Manifold ContDiff Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem contMDiff_quotient_chartCutoff
    (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (z : NilpotentLieBCHGroup L s hnil)
    (φ : OpenPartialHomeomorph (ι → ℝ) (_ ⧸ Γ))
    (hφ : ∀ v, φ v = QuotientGroup.mk (z * (basisHomeomorph e).symm v))
    (ψ : (ι → ℝ) → ℝ) (hsmooth : ContDiff ℝ ∞ ψ)
    (hsupport : tsupport (chartCutoff φ ψ) ⊆ φ.target) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ℝ) ∞
      (fun g : NilpotentLieBCHGroup L s hnil => chartCutoff φ ψ (QuotientGroup.mk g)) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := basisChartedSpace (hnil := hnil) e
  apply contMDiff_of_tsupport
  intro g hg
  have hgt : (QuotientGroup.mk g : _ ⧸ Γ) ∈ φ.target :=
    hsupport (tsupport_comp_subset_preimage (chartCutoff φ ψ) QuotientGroup.continuous_mk hg)
  have hi := contMDiffAt_quotient_chartInverse e Γ z φ hφ ∞ g hgt
  have hnear : ∀ᶠ h in 𝓝 g, (QuotientGroup.mk h : _ ⧸ Γ) ∈ φ.target :=
    QuotientGroup.continuous_mk.continuousAt (φ.open_target.mem_nhds hgt)
  apply (hsmooth.contMDiff.contMDiffAt.comp g hi).congr_of_eventuallyEq
  filter_upwards [hnear] with h hh
  exact dite_eq_left hh

end Erdos3.NilpotentLieBCHGroup

end

end OAI
