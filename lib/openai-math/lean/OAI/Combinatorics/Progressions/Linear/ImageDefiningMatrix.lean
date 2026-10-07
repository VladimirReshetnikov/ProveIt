import OAI.Combinatorics.Progressions.Estimates.RealifiedReconstruction

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem ker_id_sub_comp_eq_range {R V W : Type*} [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (φ : V →ₗ[R] W) (σ : W →ₗ[R] V) (hσ : (φ.comp σ).comp φ = φ) :
    LinearMap.ker (LinearMap.id - φ.comp σ) = LinearMap.range φ := by
  ext y
  change y - φ (σ y) = 0 ↔ ∃ x, φ x = y
  constructor
  · intro h
    exact ⟨σ y, (sub_eq_zero.mp h).symm⟩
  · rintro ⟨x, rfl⟩
    exact sub_eq_zero.mpr (DFunLike.congr_fun hσ x).symm

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem baseChange_matrix_apply [DecidableEq ι] [DecidableEq κ]
    (e : Basis ι ℚ L) (f : Basis κ ℚ M) (P : L →ₗ[ℚ] M) (x : ℝ ⊗[ℚ] L) :
    (fun i j => (LinearMap.toMatrix e f P i j : ℝ)) *ᵥ (e.baseChange ℝ).equivFun x =
      (f.baseChange ℝ).equivFun (P.baseChange ℝ x) := by
  have heq : (fun i j => (LinearMap.toMatrix e f P i j : ℝ)) =
      LinearMap.toMatrix (e.baseChange ℝ) (f.baseChange ℝ) (P.baseChange ℝ) := by
    ext i j
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, linearMap_baseChange_basis]
  rw [heq]
  simpa only [Basis.equivFun_apply] using
    LinearMap.toMatrix_mulVec_repr (e.baseChange ℝ) (f.baseChange ℝ) (P.baseChange ℝ) x

open NilpotentLieBCHGroup

variable {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem realificationMap_mem_range_iff (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) s (realification_lowerCentralSeries_eq_bot hM)) :
    g ∈ (realificationMap (hnil := hL) (hM := hM) φ).range ↔
      g.coord ∈ LinearMap.range (φ.toLinearMap.baseChange ℝ) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.coord, congrArg NilpotentLieBCHGroup.coord hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x⟩, ext hx⟩

theorem exists_realified_image_defining_matrix (e : Basis ι ℚ L) (f : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H) :
    ∃ Q : Matrix κ κ ℚ,
      (∀ i j, RationalHeightLE (Q i j)
        (2 * ((Fintype.card ι + 1) * (H * rationalKernelHeight (Fintype.card κ) H) ^ Fintype.card ι))) ∧
      ∀ g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) s (realification_lowerCentralSeries_eq_bot hM),
        g ∈ (realificationMap (hnil := hL) (hM := hM) φ).range ↔
          (fun i j => (Q i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun g.coord = 0 := by
  classical
  obtain ⟨σ, hσ, hσH⟩ := exists_bounded_linear_image_section e f φ.toLinearMap hH hentries
  let P : M →ₗ[ℚ] M := LinearMap.id - φ.toLinearMap.comp σ
  let Q := LinearMap.toMatrix f f P
  have hQ : Q = 1 - LinearMap.toMatrix e f φ.toLinearMap * LinearMap.toMatrix f e σ := by
    dsimp [Q, P]
    rw [map_sub, LinearMap.toMatrix_id, LinearMap.toMatrix_comp f e f]
  refine ⟨Q, ?_, ?_⟩
  · intro i j
    have hI : RationalHeightLE ((1 : Matrix κ κ ℚ) i j) 1 := by
      by_cases hij : i = j
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
      · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
    have hprod := rationalHeightLE_matrix_mul (LinearMap.toMatrix e f φ.toLinearMap)
      (LinearMap.toMatrix f e σ)
      (fun i j => by rw [LinearMap.toMatrix_apply]; exact hentries i j)
      (fun i j => by rw [LinearMap.toMatrix_apply]; exact hσH i j) i j
    rw [hQ]
    simpa only [Matrix.sub_apply, mul_one] using hI.sub hprod
  · intro g
    have hσR := linearMap_baseChange_image_section φ.toLinearMap σ hσ
    have hker := ker_id_sub_comp_eq_range (φ.toLinearMap.baseChange ℝ) (σ.baseChange ℝ) hσR
    have hPR : P.baseChange ℝ = LinearMap.id - (φ.toLinearMap.baseChange ℝ).comp (σ.baseChange ℝ) := by
      simp only [P, LinearMap.baseChange_sub, LinearMap.baseChange_id, LinearMap.baseChange_comp]
    rw [realificationMap_mem_range_iff, ← hker, ← hPR]
    change P.baseChange ℝ g.coord = 0 ↔ _
    rw [show (fun i j => (Q i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun g.coord =
      (f.baseChange ℝ).equivFun (P.baseChange ℝ g.coord) from baseChange_matrix_apply f f P g.coord]
    constructor
    · intro h
      rw [h, map_zero]
    · intro h
      apply (f.baseChange ℝ).equivFun.injective
      simpa only [map_zero] using h

end Erdos3

end

end OAI
