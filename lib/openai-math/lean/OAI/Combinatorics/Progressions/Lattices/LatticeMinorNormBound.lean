import OAI.Combinatorics.Progressions.Estimates.NormalizedMinorBounds
import OAI.Combinatorics.Progressions.Geometry.CoordinateMinorCovolume

namespace OAI

section

namespace Erdos3

theorem lattice_projection_all_minors_bound {ι κ E : Type*} [Fintype ι] {k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (e : κ → ι) (he : Function.Injective e)
    (H : Matrix κ (Fin k) ℝ) (hH : ∀ i j, H i j = f (b j).val (e i)) :
    ∀ q : Fin k → κ, |(H.submatrix q id).det| ≤ ZLattice.covolume Λ := by
  intro q
  by_cases hq : Function.Injective q
  · have h := abs_isometric_lattice_basis_det_le_covolume Λ b f (e ∘ q) (he.comp hq)
    have hm : Matrix.of (fun i j => f (b i).val ((e ∘ q) j)) =
        (H.submatrix q id).transpose := by
      ext i j
      exact (hH (q j) i).symm
    simpa only [hm, Matrix.det_transpose] using h
  · have hd : (H.submatrix q id).det = 0 := by
      by_contra hd
      exact hq (nonzero_row_minor_injective H q hd)
    rw [hd, abs_zero]
    exact (ZLattice.covolume_pos Λ MeasureTheory.volume).le

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem lattice_norm_le_selected_coordinates {ι E : Type*} [Fintype ι] {k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (p : Fin k → ι)
    (hp : (Matrix.of (fun i j => f (b j).val (p i))).det ≠ 0)
    (C D : ℝ) (hD : 0 < D) (hC : ZLattice.covolume Λ ≤ C)
    (hlower : 1 / D ≤ |(Matrix.of (fun i j => f (b j).val (p i))).det|)
    (x : E) :
    ‖x‖ ≤ (Fintype.card ι : ℝ) * k * (C * D) * ‖fun j => f x (p j)‖ := by
  let bR := b.ofZLatticeBasis ℝ Λ
  let g := (EuclideanSpace.equiv ι ℝ).toLinearMap.comp f.toLinearMap
  let F := Matrix.of (fun i j => g (bR j) i)
  have hF (i j) : F i j = f (b j).val i := by
    simp only [F, Matrix.of_apply, bR, Module.Basis.ofZLatticeBasis_apply]
    rfl
  have hminor : ∀ q : Fin k → ι, |(F.submatrix q id).det| ≤ C := by
    intro q
    exact (lattice_projection_all_minors_bound Λ b f id Function.injective_id F hF q).trans hC
  have hp' : (F.submatrix p id).det ≠ 0 := by
    have he : F.submatrix p id = Matrix.of (fun i j => f (b j).val (p i)) := by
      ext i j
      exact hF (p i) j
    rwa [he]
  have hlower' : 1 / D ≤ |(F.submatrix p id).det| := by
    have he : F.submatrix p id = Matrix.of (fun i j => f (b j).val (p i)) := by
      ext i j
      exact hF (p i) j
    rwa [he]
  have hC0 : 0 ≤ C := (ZLattice.covolume_pos Λ MeasureTheory.volume).le.trans hC
  have hbound := euclidean_matrix_mulVec_norm_le (F * (F.submatrix p id)⁻¹)
    (C * D) (mul_nonneg hC0 hD.le)
    (row_normalization_abs_le F p hp' C D hD hminor hlower') (fun j => f x (p j))
  have hreconstruct :
      (F * (F.submatrix p id)⁻¹) *ᵥ (fun j => f x (p j)) = g x :=
    basis_image_reconstruct_from_minor bR g p hp' x
  have he : (EuclideanSpace.equiv ι ℝ).symm
      ((F * (F.submatrix p id)⁻¹) *ᵥ (fun j => f x (p j))) = f x := by
    rw [hreconstruct]
    exact (EuclideanSpace.equiv ι ℝ).symm_apply_apply (f x)
  rw [he, f.norm_map] at hbound
  exact hbound

theorem lattice_norm_le_projection_of_grid_minor
    {ι κ E : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (e : κ → ι) (l : ℕ) (hl : 0 < l) (B : Matrix κ (Fin k) ℝ)
    (hB : ∀ i j, B i j = f (b j).val (e i))
    (hgrid : ∀ j, B.col j ∈ realDenominatorGrid l)
    (p : Fin k → κ) (hp : (B.submatrix p id).det ≠ 0)
    (C : ℝ) (hC : ZLattice.covolume Λ ≤ C) (x : E) :
    ‖x‖ ≤ (Fintype.card ι : ℝ) * k * (C * (l : ℝ) ^ k) *
      ‖fun i => f x (e i)‖ := by
  let M := B.submatrix p id
  have hm : Matrix.of (fun i j => f (b j).val ((e ∘ p) i)) = M := by
    ext i j
    exact (hB (p i) j).symm
  have hMgrid (j) : (fun i => M i j) ∈ realDenominatorGrid l := by
    obtain ⟨z, hz⟩ := hgrid j
    refine ⟨fun i => z (p i), ?_⟩
    funext i
    exact congrFun hz (p i)
  have hMlower : 1 / (l : ℝ) ^ k ≤ |M.det| := by
    simpa only [Fintype.card_fin] using one_div_pow_le_abs_grid_det M l hl hMgrid hp
  have hp' : (Matrix.of (fun i j => f (b j).val ((e ∘ p) i))).det ≠ 0 := by rwa [hm]
  have hlower : 1 / (l : ℝ) ^ k ≤
      |(Matrix.of (fun i j => f (b j).val ((e ∘ p) i))).det| := by rwa [hm]
  have hn := lattice_norm_le_selected_coordinates Λ b f (e ∘ p) hp' C ((l : ℝ) ^ k)
    (pow_pos (by exact_mod_cast hl) _) hC hlower x
  have hr : ‖fun j => f x ((e ∘ p) j)‖ ≤ ‖fun i => f x (e i)‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    exact norm_le_pi_norm (fun i => f x (e i)) (p j)
  have hC0 : 0 ≤ C := (ZLattice.covolume_pos Λ MeasureTheory.volume).le.trans hC
  exact hn.trans (mul_le_mul_of_nonneg_left hr (by positivity))

end Erdos3

end

end OAI
