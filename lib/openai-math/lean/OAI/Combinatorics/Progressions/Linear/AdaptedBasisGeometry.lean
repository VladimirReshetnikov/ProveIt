import OAI.Combinatorics.Progressions.Linear.BoundedAdaptedBasis
import OAI.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

theorem inverse_basis_entries_height (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    {H : ℕ} (hH : 1 ≤ H) (hb : ∀ j i, RationalHeightLE (e.repr (b j) i) H) :
    ∀ i j, RationalHeightLE (b.repr (e i) j) (rationalSolveHeight (Fintype.card κ) H) := by
  classical
  let A := LinearMap.toMatrix b e (LinearMap.id : L →ₗ[ℚ] L)
  let C := LinearMap.toMatrix e b (LinearMap.id : L →ₗ[ℚ] L)
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    dsimp only [A]
    rw [LinearMap.toMatrix_apply]
    exact hb j i
  have hli : LinearIndependent ℚ A.col :=
    Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e LinearMap.id Function.injective_id)
  obtain ⟨P, hPA, hPH⟩ := exists_bounded_rational_left_inverse A hli hH hA
  have hAC : A * C = 1 := by
    dsimp only [A, C]
    rw [← LinearMap.toMatrix_comp, LinearMap.id_comp, LinearMap.toMatrix_id]
  have hPC : P = C := by
    calc
      P = P * 1 := (Matrix.mul_one P).symm
      _ = P * (A * C) := by rw [hAC]
      _ = (P * A) * C := (Matrix.mul_assoc P A C).symm
      _ = C := by rw [hPA, Matrix.one_mul]
  intro i j
  have h := hPH j i
  rw [hPC] at h
  simpa only [C, LinearMap.toMatrix_apply, LinearMap.id_apply] using h

theorem basis_change_structure_height (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    {H : ℕ} (hH : 1 ≤ H) (hb : ∀ j i, RationalHeightLE (e.repr (b j) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
      (rationalLieStructureHeight (Fintype.card ι) (max H (rationalSolveHeight (Fintype.card κ) H))) := by
  classical
  obtain ⟨_, _, _, h⟩ := exists_bounded_lie_embedding_retraction b e
    (LieHom.id : L →ₗ⁅ℚ⁆ L) Function.injective_id hH hc (by
      intro i j
      rw [LinearMap.toMatrix_apply]
      exact hb j i)
  exact h

theorem exists_basis_change_grid_exp_bound (e : Basis ι ℚ L) (b : Basis κ ℚ L)
    {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hb : ∀ j i, RationalHeightLE (e.repr (b j) i) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hr : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ ∧
      bchSubgroupCoordinates b Γ ⊆ denominatorGrid N := by
  classical
  have hid : NilpotentLieBCHGroup.map (hnil := hnil) (hM := hnil)
      (LieHom.id : L →ₗ⁅ℚ⁆ L) = MonoidHom.id _ := by
    ext g
    rfl
  simpa only [hid, Subgroup.comap_id] using exists_bchSubgroup_comap_grid_exp_bound
    (hM := hnil) b e (LieHom.id : L →ₗ⁅ℚ⁆ L) Function.injective_id Γ hH hl
      (by intro i j; rw [LinearMap.toMatrix_apply]; exact hb j i)
      hinner houter hp hd hr hHp hlp

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L)

theorem exists_adapted_basis_and_grid {η : Fin (s + 1) → Type*}
    (v : ∀ i, η i → F.layer (i.val + 1))
    (hspan : ∀ i, Submodule.span ℚ (Set.range (v i)) = ⊤)
    (Γ : Subgroup F.Group) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ i j k, RationalHeightLE (e.repr (v i j : L) k) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ) (N : ℕ),
      Monotone w ∧ IsCentralLieBasis b ∧
      (∀ i, F.layer i = Submodule.span ℚ (b '' {j | i ≤ w j})) ∧
      (∀ j i, RationalHeightLE (e.repr (b j) i) H) ∧
      (∀ i j, RationalHeightLE (b.repr (e i) j) (rationalSolveHeight (finrank ℚ L) H)) ∧
      (∀ i j k, ((lieStructureConstants b i j k).num.natAbs : ℝ) ≤ Real.exp ((p + 2) ^ 11) ∧
        ((lieStructureConstants b i j k).den : ℝ) ≤ Real.exp ((p + 2) ^ 11)) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ ∧
      bchSubgroupCoordinates b Γ ⊆ denominatorGrid N := by
  obtain ⟨b, w, hw, _, hcentral, hb, hlayer⟩ := F.exists_bounded_sorted_adapted_basis e v hspan hv
  have hr : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ p := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis e] using hd
  obtain ⟨N, hN, hNp, hin, hout⟩ :=
    exists_basis_change_grid_exp_bound e b Γ hH hl hb hinner houter hp hd hr hHp hlp
  have hbinv := inverse_basis_entries_height e b hH hb
  have hstructure := basis_change_structure_height e b hH hb hc
  have hbudget := rationalLieStructureHeight_inverse_budget (Fintype.card ι)
    (Fintype.card (Fin (finrank ℚ L))) H hp hd hr hHp
  refine ⟨b, w, N, hw, hcentral, hlayer, hb, ?_, ?_, hN, hNp, hin, hout⟩
  · simpa only [Fintype.card_fin] using hbinv
  · intro i j k
    exact ⟨(Nat.cast_le.mpr (hstructure i j k).1).trans hbudget,
      (Nat.cast_le.mpr (hstructure i j k).2).trans hbudget⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
