import OAI.Combinatorics.Progressions.Estimates.ControlledSurjectiveReconstruction

namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped Matrix TensorProduct

theorem matrix_mulVec_fine_grid {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix ι κ ℚ) (l : ℕ) :
    scaledIntegerGrid (l * matrixDenominator S) ⊆ S.mulVec ⁻¹' scaledIntegerGrid l := by
  classical
  rintro y ⟨z, rfl⟩
  obtain ⟨w, hw⟩ := integralVector_denominator_mulVec S (fun j => (z j : ℚ)) ⟨z, fun _ => rfl⟩
  refine ⟨w, ?_⟩
  rw [Matrix.mulVec_smul]
  ext i
  have hi := hw i
  change (matrixDenominator S : ℚ) * (S *ᵥ fun j => (z j : ℚ)) i = (w i : ℚ) at hi
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
  rw [mul_assoc, hi]

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem real_image_lattice_lift [DecidableEq ι] [DecidableEq κ]
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M) (σ : M →ₗ[ℚ] L)
    (hσ : (φ.toLinearMap.comp σ).comp φ.toLinearMap = φ.toLinearMap)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Λ : Subgroup (NilpotentLieBCHGroup M s hM)) (l B : ℕ)
    (hΓ : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (hΛ : bchSubgroupCoordinates f Λ ⊆ scaledIntegerGrid B)
    (hdiv : l * matrixDenominator (LinearMap.toMatrix f e σ) ∣ B) :
    Λ.map realificationHom ⊓ (realificationMap (hnil := hL) (hM := hM) φ).range ≤
      (Γ.map realificationHom).map (realificationMap (hnil := hL) (hM := hM) φ) := by
  rintro g ⟨hg, himage⟩
  obtain ⟨γ, hγ, rfl⟩ := hg
  obtain ⟨x, hx⟩ := himage
  have hxcoord := congrArg NilpotentLieBCHGroup.coord hx
  change φ.toLinearMap.baseChange ℝ x.coord = (1 : ℝ) ⊗ₜ[ℚ] γ.coord at hxcoord
  have hsection := DFunLike.congr_fun (linearMap_baseChange_image_section φ.toLinearMap σ hσ) x.coord
  change φ.toLinearMap.baseChange ℝ (σ.baseChange ℝ (φ.toLinearMap.baseChange ℝ x.coord)) =
    φ.toLinearMap.baseChange ℝ x.coord at hsection
  rw [hxcoord] at hsection
  have hpre : φ (σ γ.coord) = γ.coord := by
    apply rationalLieInclusion_injective f
    change (1 : ℝ) ⊗ₜ[ℚ] φ (σ γ.coord) = (1 : ℝ) ⊗ₜ[ℚ] γ.coord
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul] at hsection
    exact hsection
  let a : NilpotentLieBCHGroup L s hL := ⟨σ γ.coord⟩
  have ha : a ∈ Γ := by
    apply (bchSubgroupCoordinates_repr e Γ a).mp
    apply hΓ
    have hy := scaledIntegerGrid_subset_of_dvd hdiv
      (hΛ ((bchSubgroupCoordinates_repr f Λ γ).mpr hγ))
    have hs := matrix_mulVec_fine_grid (LinearMap.toMatrix f e σ) l hy
    change LinearMap.toMatrix f e σ *ᵥ f.equivFun γ.coord ∈ scaledIntegerGrid l at hs
    rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply] at hs
    exact hs
  refine ⟨realificationHom a, ⟨a, ha, rfl⟩, ?_⟩
  rw [realificationMap_realificationHom]
  apply congrArg realificationHom
  exact ext hpre

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem exists_image_lattice_subgroup (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (Γ : Subgroup (NilpotentLieBCHGroup L s hL))
    (Δ : Subgroup (NilpotentLieBCHGroup M s hM))
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (hH : 1 ≤ H)
    (hΓ : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (hΔ : scaledIntegerGrid m ⊆ bchSubgroupCoordinates f Δ)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H) :
    ∃ (B : ℕ) (Λ : Subgroup (NilpotentLieBCHGroup M s hM)),
      0 < B ∧ m ∣ B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (Fintype.card κ ^ 3) *
        (m * (l * rationalKernelHeight (Fintype.card κ) H ^ (Fintype.card ι * Fintype.card κ))) ∧
      Λ ≤ Δ ∧ bchSubgroupCoordinates f Λ = scaledIntegerGrid B ∧
      Λ.map realificationHom ⊓ (realificationMap (hnil := hL) (hM := hM) φ).range ≤
        (Γ.map realificationHom).map (realificationMap (hnil := hL) (hM := hM) φ) := by
  classical
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_image_section e f φ.toLinearMap hH hentries
  let D := matrixDenominator (LinearMap.toMatrix f e σ)
  have hD : 0 < D := matrixDenominator_pos _
  have hDb : D ≤ rationalKernelHeight (Fintype.card κ) H ^ (Fintype.card ι * Fintype.card κ) := by
    apply matrixDenominator_le
    intro i j
    rw [LinearMap.toMatrix_apply]
    exact hσH i j
  let q := m * (l * D)
  have hq : 0 < q := Nat.mul_pos hm (Nat.mul_pos hl hD)
  have hΔq : scaledIntegerGrid q ⊆ bchSubgroupCoordinates f Δ :=
    (scaledIntegerGrid_subset_of_dvd (dvd_mul_right m (l * D))).trans hΔ
  obtain ⟨B, Λ, hB, hqB, hBb, hΛ, hgrid⟩ := exists_integral_grid_subgroup f hM Δ q hq hc hΔq
  refine ⟨B, Λ, hB, (dvd_mul_right m (l * D)).trans hqB, ?_, hΛ, hgrid, ?_⟩
  · exact hBb.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left m (Nat.mul_le_mul_left l hDb)))
  · apply real_image_lattice_lift e f φ σ hσ Γ Λ l B hΓ
    · exact hgrid.le
    · exact (dvd_mul_left (l * D) m).trans hqB

namespace NilpotentLieFiltration

theorem exists_image_lattice_cover (F : NilpotentLieFiltration M s)
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (φ : L →ₗ⁅ℚ⁆ M)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) (Δ : Subgroup F.Group)
    (l m H : ℕ) (hl : 0 < l) (hm : 0 < m) (hH : 1 ≤ H)
    (hΓ : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (hΔin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates f Δ)
    (hΔout : bchSubgroupCoordinates f Δ ⊆ denominatorGrid m)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants f i j k) H) :
    ∃ (B : ℕ) (Λ : Subgroup F.Group),
      0 < B ∧ B ≤ bchIntegralDenominatorBound s * H ^ (Fintype.card κ ^ 3) *
        (m * (l * rationalKernelHeight (Fintype.card κ) H ^ (Fintype.card ι * Fintype.card κ))) ∧
      Λ ≤ Δ ∧ (Λ.subgroupOf Δ).Characteristic ∧ (Λ.subgroupOf Δ).Normal ∧
      (Λ.subgroupOf Δ).FiniteIndex ∧ Λ.relIndex Δ ≤ (m * B) ^ Fintype.card κ ∧
      scaledIntegerGrid ((m * B) * m) ⊆ bchSubgroupCoordinates f Λ ∧
      bchSubgroupCoordinates f Λ ⊆ denominatorGrid ((m * B) * m) ∧
      Λ.map realificationHom ⊓
        (realificationMap (hnil := hL) (hM := F.lowerCentralSeries_eq_bot) φ).range ≤
        (Γ.map realificationHom).map
          (realificationMap (hnil := hL) (hM := F.lowerCentralSeries_eq_bot) φ) := by
  obtain ⟨B, Λ₀, hB, _, hBb, _, hgrid, hlift⟩ := exists_image_lattice_subgroup e f φ Γ Δ
    l m H hl hm hH hΓ hΔin hentries hc
  obtain ⟨Λ, hΛ₀, hΛ, hchar, hnormal, hfinite, hindex, hin, hout⟩ :=
    F.exists_sharp_normal_cover f Δ Λ₀ m B hm hB hΔin hΔout hgrid.ge
  refine ⟨B, Λ, hB, hBb, hΛ, hchar, hnormal, hfinite, hindex, hin, hout, ?_⟩
  exact le_trans (inf_le_inf_right _ (Subgroup.map_mono hΛ₀)) hlift

end NilpotentLieFiltration
end Erdos3

end

end OAI
