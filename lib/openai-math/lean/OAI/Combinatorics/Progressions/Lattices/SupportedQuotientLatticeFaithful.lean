/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.CosetPairInjective
import OAI.Combinatorics.Progressions.Geometry.RealSupportedQuotientCoordinates
import OAI.Combinatorics.Progressions.Sampling.SupportedQuotientExactGrid

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem mem_realification_integral_lattice_iff (b : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (N : ℕ)
    (hgrid : bchSubgroupCoordinates b Γ = scaledIntegerGrid N)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    g ∈ Γ.map realificationHom ↔
      ∃ z : ι → ℤ, ∀ i, (b.baseChange ℝ).repr g.coord i = (N : ℝ) * (z i : ℝ) := by
  constructor
  · intro hg
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
    have hc := (bchSubgroupCoordinates_repr b Γ a).mpr ha
    rw [hgrid] at hc
    obtain ⟨z, hz⟩ := hc
    refine ⟨z, fun i => ?_⟩
    rw [← Basis.equivFun_apply, realificationHom_coordinates]
    have hi := congrFun hz i
    change b.repr a.coord i = (N : ℚ) * (z i : ℚ) at hi
    change (b.repr a.coord i : ℝ) = _
    rw [hi]
    push_cast
    rfl
  · rintro ⟨z, hz⟩
    let a : NilpotentLieBCHGroup L s hnil :=
      ⟨b.equivFun.symm (fun i => (N : ℚ) * (z i : ℚ))⟩
    have ha : a ∈ Γ := by
      apply (bchSubgroupCoordinates_repr b Γ a).mp
      rw [hgrid]
      change b.equivFun (b.equivFun.symm _) ∈ scaledIntegerGrid N
      rw [LinearEquiv.apply_symm_apply]
      exact ⟨z, rfl⟩
    refine Subgroup.mem_map.mpr ⟨a, ha, ?_⟩
    apply NilpotentLieBCHGroup.ext
    apply (b.baseChange ℝ).equivFun.injective
    rw [realificationHom_coordinates]
    funext i
    change (b.equivFun (b.equivFun.symm _) i : ℝ) = _
    rw [LinearEquiv.apply_symm_apply]
    push_cast
    exact (hz i).symm

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t u : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

include hspan in
theorem realQuotientStep_integral_coordinates (Γ : Subgroup F.Group) (N : ℕ)
    (hgrid : bchSubgroupCoordinates b Γ = scaledIntegerGrid N)
    (g : F.realification.Group)
    (hg : F.realQuotientStepHom I hI g ∈
      (Γ.map (F.quotientStepHom I hI)).map realificationHom) :
    ∃ z : {i // i ∉ S} → ℤ, ∀ i : {i // i ∉ S},
      (b.baseChange ℝ).repr g.coord i = (N : ℝ) * (z i : ℝ) := by
  let bq : Basis {i // i ∉ S} ℚ (L ⧸ I) := supportedQuotientBasis b I.toSubmodule S hspan
  have hq : bchSubgroupCoordinates bq (Γ.map (F.quotientStepHom I hI)) = scaledIntegerGrid N :=
    F.quotientStep_exact_grid_supported b I hI S hspan Γ N hgrid
  obtain ⟨z, hz⟩ := (mem_realification_integral_lattice_iff (L := L ⧸ I)
    (hnil := (F.quotientLie I hI).lowerCentralSeries_eq_bot) bq
    (Γ.map (F.quotientStepHom I hI)) N hq (F.realQuotientStepHom I hI g)).mp hg
  refine ⟨z, fun i => ?_⟩
  have hi := hz i
  change ((supportedQuotientBasis b I.toSubmodule S hspan).baseChange ℝ).repr
    (I.toSubmodule.mkQ.baseChange ℝ g.coord) i = _ at hi
  rwa [realSupportedQuotientBasis_repr_mk] at hi

theorem realQuotientStep_lattice_le (Γ : Subgroup F.Group) :
    Γ.map realificationHom ≤
      ((Γ.map (F.quotientStepHom I hI)).map realificationHom).comap
        (F.realQuotientStepHom I hI) := by
  rw [F.realQuotientStepHom_lattice]
  exact Subgroup.le_comap_map (F.realQuotientStepHom I hI) (Γ.map realificationHom)

noncomputable def realQuotientCosetMap (Γ : Subgroup F.Group) :
    (F.realification.Group ⧸ Γ.map realificationHom) →
      ((F.quotientLie I hI).realification.Group ⧸
        (Γ.map (F.quotientStepHom I hI)).map realificationHom) :=
  cosetMap _ _ (F.realQuotientStepHom I hI) (F.realQuotientStep_lattice_le I hI Γ)

include hspan in
theorem realQuotientPair_lattice_detect
    (J : LieIdeal ℚ L) (hJ : F.layer (u + 1) ≤ J.toSubmodule)
    (T : Set ι) [DecidablePred (· ∈ T)]
    (hspanT : J.toSubmodule = Submodule.span ℚ (b '' T))
    (hcover : ∀ i : ι, i ∉ S ∨ i ∉ T)
    (Γ : Subgroup F.Group) (N : ℕ)
    (hgrid : bchSubgroupCoordinates b Γ = scaledIntegerGrid N)
    (g : F.realification.Group)
    (hgI : F.realQuotientStepHom I hI g ∈
      (Γ.map (F.quotientStepHom I hI)).map realificationHom)
    (hgJ : F.realQuotientStepHom J hJ g ∈
      (Γ.map (F.quotientStepHom J hJ)).map realificationHom) :
    g ∈ Γ.map realificationHom := by
  classical
  obtain ⟨zI, hzI⟩ := F.realQuotientStep_integral_coordinates b I hI S hspan Γ N hgrid g hgI
  obtain ⟨zJ, hzJ⟩ := F.realQuotientStep_integral_coordinates b J hJ T hspanT Γ N hgrid g hgJ
  apply (mem_realification_integral_lattice_iff b Γ N hgrid g).mpr
  let z : ι → ℤ := fun i => if hi : i ∉ S then zI ⟨i, hi⟩
    else zJ ⟨i, (hcover i).resolve_left hi⟩
  refine ⟨z, fun i => ?_⟩
  by_cases hi : i ∉ S
  · simpa only [z, dite_eq_left hi] using hzI ⟨i, hi⟩
  · simpa only [z, dite_eq_right hi] using hzJ ⟨i, (hcover i).resolve_left hi⟩

include hspan in
theorem realQuotientCosetPair_injective
    (J : LieIdeal ℚ L) (hJ : F.layer (u + 1) ≤ J.toSubmodule)
    (T : Set ι) [DecidablePred (· ∈ T)]
    (hspanT : J.toSubmodule = Submodule.span ℚ (b '' T))
    (hcover : ∀ i : ι, i ∉ S ∨ i ∉ T)
    (Γ : Subgroup F.Group) (N : ℕ)
    (hgrid : bchSubgroupCoordinates b Γ = scaledIntegerGrid N) :
    Function.Injective (fun x =>
      (F.realQuotientCosetMap I hI Γ x, F.realQuotientCosetMap J hJ Γ x)) :=
  cosetPairMap_injective _ _ _ _ _ _ _
    (F.realQuotientPair_lattice_detect b I hI S hspan J hJ T hspanT hcover Γ N hgrid)

end Erdos3.NilpotentLieFiltration

end

end OAI
