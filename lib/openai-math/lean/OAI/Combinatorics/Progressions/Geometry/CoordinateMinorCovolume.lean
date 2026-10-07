/- Modified for ProveIt: import the attributed Mathlib exterior-power
backport. Mathematical statements and proofs unchanged. -/
import OAI.Compat.ExteriorPower
import OAI.Combinatorics.Progressions.Lattices.LatticeSheetHaar

namespace OAI

section

namespace Erdos3

open RealInnerProductSpace

theorem exterior_norm_eq_sqrt_gram {r : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (v : Fin r → E) :
    ‖exteriorPower.ιMulti ℝ r v‖ = Real.sqrt (Matrix.gram ℝ v).det := by
  have hs : ‖exteriorPower.ιMulti ℝ r v‖ ^ 2 = (Matrix.gram ℝ v).det := by
    rw [← real_inner_self_eq_norm_sq]
    exact exteriorPower.inner_ιMulti_self v
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

theorem abs_coordinate_det_le_sqrt_gram {r : ℕ} {ι : Type*} [Fintype ι]
    (v : Fin r → EuclideanSpace ℝ ι) (p : Fin r → ι) (hp : Function.Injective p) :
    |(Matrix.of (fun i j => v i (p j))).det| ≤ Real.sqrt (Matrix.gram ℝ v).det := by
  classical
  let e : Fin r → EuclideanSpace ℝ ι := fun i => EuclideanSpace.single (p i) 1
  let u := exteriorPower.ιMulti ℝ r e
  let w := exteriorPower.ιMulti ℝ r v
  have he : Orthonormal ℝ e := EuclideanSpace.orthonormal_single.comp p hp
  have hgram : Matrix.gram ℝ e = 1 := Matrix.gram_eq_one_iff_orthonormal.mpr he
  have hu : ‖u‖ = 1 := by
    have hs : ‖u‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      change inner ℝ (exteriorPower.ιMulti ℝ r e) (exteriorPower.ιMulti ℝ r e) = 1
      rw [exteriorPower.inner_ιMulti_self, hgram, Matrix.det_one]
    nlinarith [norm_nonneg u]
  have hi : inner ℝ u w = (Matrix.of (fun i j => v i (p j))).det := by
    change inner ℝ (exteriorPower.ιMulti ℝ r e) (exteriorPower.ιMulti ℝ r v) = _
    rw [exteriorPower.inner_ιMulti_ιMulti]
    congr 1
    ext i j
    simp [e, EuclideanSpace.inner_single_left]
  have h := abs_real_inner_le_norm u w
  rw [hi, hu, one_mul] at h
  exact h.trans_eq (exterior_norm_eq_sqrt_gram v)

theorem abs_lattice_basis_coordinate_det_le_covolume {r : ℕ} {ι : Type*} [Fintype ι]
    (Z : Submodule ℝ (EuclideanSpace ℝ ι))
    (Λ : Submodule ℤ Z) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin r) ℤ Λ) (p : Fin r → ι) (hp : Function.Injective p) :
    |(Matrix.of (fun i j => (b i).val.val (p j))).det| ≤ ZLattice.covolume Λ := by
  have hs : ZLattice.covolume Λ ^ 2 =
      (Matrix.gram ℝ (fun i : Fin r => (b i).val.val)).det := by
    rw [lattice_covolume_sq_eq_gram Λ b]
    congr 1
    ext i j
    simp only [Matrix.gram_apply, Module.Basis.ofZLatticeBasis_apply]
    rfl
  have h := abs_coordinate_det_le_sqrt_gram (fun i : Fin r => (b i).val.val) p hp
  rw [← hs, Real.sqrt_sq (ZLattice.covolume_pos Λ MeasureTheory.volume).le] at h
  exact h

theorem abs_isometric_lattice_basis_det_le_covolume {r : ℕ} {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin r) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (p : Fin r → ι) (hp : Function.Injective p) :
    |(Matrix.of (fun i j => f (b i).val (p j))).det| ≤ ZLattice.covolume Λ := by
  have hs : ZLattice.covolume Λ ^ 2 =
      (Matrix.gram ℝ (fun i : Fin r => f (b i).val)).det := by
    rw [lattice_covolume_sq_eq_gram Λ b]
    congr 1
    ext i j
    simp only [Matrix.gram_apply, Module.Basis.ofZLatticeBasis_apply, LinearIsometry.inner_map_map]
  have h := abs_coordinate_det_le_sqrt_gram (fun i : Fin r => f (b i).val) p hp
  rw [← hs, Real.sqrt_sq (ZLattice.covolume_pos Λ MeasureTheory.volume).le] at h
  exact h

end Erdos3

end

end OAI
