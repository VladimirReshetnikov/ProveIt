import OAI.Combinatorics.Progressions.Geometry.SupportedLieQuotient

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

theorem quotientStep_inner_grid_supported (Γ : Subgroup F.Group) {N : ℕ}
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ) :
    scaledIntegerGrid N ⊆ bchSubgroupCoordinates (supportedQuotientBasis b I.toSubmodule S hspan)
      (Γ.map (F.quotientStepHom I hI)) := by
  classical
  rintro x ⟨z, rfl⟩
  let y : ι → ℚ := fun i => if hi : i ∈ S then 0 else (N : ℚ) * (z ⟨i, hi⟩ : ℚ)
  have hy : y ∈ scaledIntegerGrid N := by
    refine ⟨fun i => if hi : i ∈ S then 0 else z ⟨i, hi⟩, ?_⟩
    funext i
    dsimp [y]
    split_ifs <;> simp
  have hg : (⟨b.equivFun.symm y⟩ : F.Group) ∈ Γ := hin hy
  apply Subgroup.mem_map.mpr
  refine ⟨⟨b.equivFun.symm y⟩, hg, ?_⟩
  apply NilpotentLieBCHGroup.ext
  apply (supportedQuotientBasis b I.toSubmodule S hspan).equivFun.injective
  funext i
  rw [LinearEquiv.apply_symm_apply]
  change (supportedQuotientBasis b I.toSubmodule S hspan).repr
    (I.toSubmodule.mkQ (b.equivFun.symm y)) i = _
  rw [supportedQuotientBasis_repr_mk, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  simp only [y, i.property, dite_false, Pi.smul_apply, smul_eq_mul]

theorem quotientStep_outer_grid_supported (Γ : Subgroup F.Group) {N : ℕ}
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) :
    bchSubgroupCoordinates (supportedQuotientBasis b I.toSubmodule S hspan)
      (Γ.map (F.quotientStepHom I hI)) ⊆ denominatorGrid N := by
  classical
  intro x hx
  obtain ⟨g, hg, he⟩ := Subgroup.mem_map.mp hx
  have hgc : b.equivFun g.coord ∈ bchSubgroupCoordinates b Γ := by
    change (⟨b.equivFun.symm (b.equivFun g.coord)⟩ : F.Group) ∈ Γ
    simpa only [LinearEquiv.symm_apply_apply] using hg
  obtain ⟨z, hz⟩ := hout hgc
  have hxrepr (i : {i // i ∉ S}) : x i = b.equivFun g.coord i := by
    have hec := congrArg NilpotentLieBCHGroup.coord he
    have hr := congrArg (fun v => (supportedQuotientBasis b I.toSubmodule S hspan).equivFun v i) hec
    rw [LinearEquiv.apply_symm_apply] at hr
    change (supportedQuotientBasis b I.toSubmodule S hspan).repr
      (I.toSubmodule.mkQ g.coord) i = x i at hr
    rw [supportedQuotientBasis_repr_mk] at hr
    exact hr.symm
  refine ⟨fun i => z i, fun i => ?_⟩
  change (N : ℚ) * x i = (z i : ℚ)
  rw [hxrepr]
  exact hz i

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) [DecidablePred (· ∈ S)]
  (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

theorem quotientStep_exact_grid_supported (Γ : Subgroup F.Group) (N : ℕ)
    (hgrid : bchSubgroupCoordinates b Γ = scaledIntegerGrid N) :
    bchSubgroupCoordinates (supportedQuotientBasis b I.toSubmodule S hspan)
      (Γ.map (F.quotientStepHom I hI)) = scaledIntegerGrid N := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨g, hg, he⟩ := Subgroup.mem_map.mp hx
    have hgc := (bchSubgroupCoordinates_repr b Γ g).mpr hg
    rw [hgrid] at hgc
    obtain ⟨z, hz⟩ := hgc
    refine ⟨fun i => z i, ?_⟩
    funext i
    have hr := congrArg
      (fun v : (F.quotientLie I hI).Group =>
        (supportedQuotientBasis b I.toSubmodule S hspan).equivFun v.coord i) he
    rw [LinearEquiv.apply_symm_apply] at hr
    change (supportedQuotientBasis b I.toSubmodule S hspan).repr
      (I.toSubmodule.mkQ g.coord) i = x i at hr
    rw [supportedQuotientBasis_repr_mk] at hr
    exact hr.symm.trans (congrFun hz i)
  · exact F.quotientStep_inner_grid_supported b I hI S hspan Γ
      (by rw [hgrid])

end Erdos3.NilpotentLieFiltration

end

end OAI
