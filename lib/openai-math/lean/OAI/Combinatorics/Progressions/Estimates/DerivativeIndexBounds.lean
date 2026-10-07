/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.CovolumeFactorBounds
import OAI.Combinatorics.Progressions.Estimates.HorizontalPivotExclusion
import OAI.Combinatorics.Progressions.Estimates.LowerTriangularMinor
import OAI.Combinatorics.Progressions.Geometry.CoordinateMinorCovolume
import OAI.Combinatorics.Progressions.Lattices.EuclideanLatticeGraph
import OAI.Combinatorics.Progressions.Linear.DerivativeVerticalBasis
import OAI.Combinatorics.Progressions.Linear.EuclideanHorizontalProjection
import OAI.Combinatorics.Progressions.Probability.EuclideanDerivativeDensityCovolume

namespace OAI

section

namespace Erdos3

theorem weighted_row_minor_det {m k : ℕ} (N : Matrix (Fin m) (Fin k) ℝ)
    (w : Fin m → ℝ) (p : Fin k → Fin m) :
    (Matrix.of (fun i j => w (p i) * N (p i) j)).det =
      (∏ i, w (p i)) * (N.submatrix p id).det := by
  have he : Matrix.of (fun i j => w (p i) * N (p i) j) =
      Matrix.diagonal (fun i => w (p i)) * N.submatrix p id := by
    ext i j
    simp [Matrix.diagonal_mul]
  rw [he, Matrix.det_mul, Matrix.det_diagonal]

theorem exists_weighted_minor_lower_bound {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℝ) (hA : LinearIndependent ℝ A.col)
    (l : ℕ) (hl : 0 < l) (hgrid : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l)
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0) (hdiag : ∀ i, M i i = 1)
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ p : Fin k → Fin m, Function.Injective p ∧
      1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤
        |(Matrix.of (fun i j => w (p i) * (M * A) (p i) j)).det| := by
  obtain ⟨p, hp, hdet, hpreserve⟩ := exists_preserved_nonzero_row_minor A hA
  have hsubgrid : ∀ j, (fun i => (A.submatrix p id) i j) ∈ realDenominatorGrid l := by
    intro j
    obtain ⟨z, hz⟩ := hgrid j
    exact ⟨fun i => z (p i), funext (fun i => congrFun hz (p i))⟩
  have hminor := one_div_pow_le_abs_grid_det (A.submatrix p id) l hl hsubgrid hdet
  simp only [Fintype.card_fin] at hminor
  refine ⟨p, hp, ?_⟩
  rw [weighted_row_minor_det, hpreserve M hM hdiag, abs_mul,
    abs_of_pos (Finset.prod_pos (fun i _ => hw (p i)))]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_right hminor (Finset.prod_nonneg (fun i _ => (hw (p i)).le))

theorem weighted_lattice_covolume_lower {ι : Type*} [Fintype ι] {m k : ℕ}
    (Z : Submodule ℝ (EuclideanSpace ℝ ι))
    (Λ : Submodule ℤ Z) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (e : Fin m → ι) (he : Function.Injective e)
    (A : Matrix (Fin m) (Fin k) ℝ) (hA : LinearIndependent ℝ A.col)
    (l : ℕ) (hl : 0 < l) (hgrid : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l)
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0) (hdiag : ∀ i, M i i = 1)
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (hcoord : ∀ j i, (b j).val.val (e i) = w i * (M * A) i j) :
    ∃ p : Fin k → Fin m, Function.Injective p ∧
      1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤ ZLattice.covolume Λ := by
  obtain ⟨p, hp, hlower⟩ := exists_weighted_minor_lower_bound A hA l hl hgrid M hM hdiag w hw
  refine ⟨p, hp, hlower.trans ?_⟩
  have hupper := abs_lattice_basis_coordinate_det_le_covolume Z Λ b (e ∘ p) (he.comp hp)
  have hmatrix : Matrix.of (fun i j => (b i).val.val ((e ∘ p) j)) =
      (Matrix.of (fun i j => w (p i) * (M * A) (p i) j)).transpose := by
    ext i j
    exact hcoord i (p j)
  simpa only [hmatrix, Matrix.det_transpose] using hupper

theorem weighted_isometric_lattice_covolume_lower {ι E : Type*} [Fintype ι] {m k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (e : Fin m → ι) (he : Function.Injective e)
    (A : Matrix (Fin m) (Fin k) ℝ) (hA : LinearIndependent ℝ A.col)
    (l : ℕ) (hl : 0 < l) (hgrid : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l)
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0) (hdiag : ∀ i, M i i = 1)
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (hcoord : ∀ j i, f (b j).val (e i) = w i * (M * A) i j) :
    ∃ p : Fin k → Fin m, Function.Injective p ∧
      1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤ ZLattice.covolume Λ := by
  obtain ⟨p, hp, hlower⟩ := exists_weighted_minor_lower_bound A hA l hl hgrid M hM hdiag w hw
  refine ⟨p, hp, hlower.trans ?_⟩
  have hupper := abs_isometric_lattice_basis_det_le_covolume Λ b f (e ∘ p) (he.comp hp)
  have hmatrix : Matrix.of (fun i j => f (b i).val ((e ∘ p) j)) =
      (Matrix.of (fun i j => w (p i) * (M * A) (p i) j)).transpose := by
    ext i j
    exact hcoord i (p j)
  simpa only [hmatrix, Matrix.det_transpose] using hupper

end Erdos3

end

section

namespace Erdos3

theorem weighted_isometric_lattice_minor_data {ι E : Type*} [Fintype ι] {m k : ℕ}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (b : Module.Basis (Fin k) ℤ Λ) (f : E →ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (e : Fin m → ι) (he : Function.Injective e)
    (A : Matrix (Fin m) (Fin k) ℝ) (hA : LinearIndependent ℝ A.col)
    (l : ℕ) (hl : 0 < l) (hgrid : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l)
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0) (hdiag : ∀ i, M i i = 1)
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (hcoord : ∀ j i, f (b j).val (e i) = w i * (M * A) i j) :
    ∃ p : Fin k → Fin m, Function.Injective p ∧ (A.submatrix p id).det ≠ 0 ∧
      1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤ ZLattice.covolume Λ := by
  obtain ⟨p, hp, hdet, hpreserve⟩ := exists_preserved_nonzero_row_minor A hA
  have hsubgrid : ∀ j, (fun i => (A.submatrix p id) i j) ∈ realDenominatorGrid l := by
    intro j
    obtain ⟨z, hz⟩ := hgrid j
    exact ⟨fun i => z (p i), funext (fun i => congrFun hz (p i))⟩
  have hminor := one_div_pow_le_abs_grid_det (A.submatrix p id) l hl hsubgrid hdet
  simp only [Fintype.card_fin] at hminor
  have hlower : 1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤
      |(Matrix.of (fun i j => w (p i) * (M * A) (p i) j)).det| := by
    rw [weighted_row_minor_det, hpreserve M hM hdiag, abs_mul,
      abs_of_pos (Finset.prod_pos (fun i _ => hw (p i)))]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hminor (Finset.prod_nonneg (fun i _ => (hw (p i)).le))
  refine ⟨p, hp, hdet, hlower.trans ?_⟩
  have hupper := abs_isometric_lattice_basis_det_le_covolume Λ b f (e ∘ p) (he.comp hp)
  have hmatrix : Matrix.of (fun i j => f (b i).val ((e ∘ p) j)) =
      (Matrix.of (fun i j => w (p i) * (M * A) (p i) j)).transpose := by
    ext i j
    exact hcoord i (p j)
  simpa only [hmatrix, Matrix.det_transpose] using hupper

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem lower_triangular_horizontal_row {m a : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0)
    (hblock : ∀ i j, i.val < a → j.val < a → M i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (i : Fin m) (hi : i.val < a) (j : Fin m) :
    M i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j := by
  by_cases hj : j.val < a
  · exact hblock i j hi hj
  · have hij : i < j := by omega
    rw [hM i j hij, Matrix.one_apply, ite_eq_right (ne_of_lt hij)]

theorem lower_triangular_horizontal_mulVec {m a : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0)
    (hblock : ∀ i j, i.val < a → j.val < a → M i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (x : Fin m → ℝ) (i : Fin m) (hi : i.val < a) : (M *ᵥ x) i = x i := by
  calc
    _ = ((1 : Matrix (Fin m) (Fin m) ℝ) *ᵥ x) i := by
      simp only [Matrix.mulVec, dotProduct, lower_triangular_horizontal_row M hM hblock i hi]
    _ = x i := congrFun (Matrix.one_mulVec x) i

theorem euclideanVerticalMap_horizontal {σ : Type*} {m a : ℕ}
    (scale : Fin m → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (x : Fin m → ℝ) (i : Fin m) (hi : i.val < a) :
    euclideanVerticalMap (σ := σ) scale hscale A x (Sum.inr i) = x i := by
  rw [euclideanVerticalMap_apply_inr, hscalehor i hi, one_mul]
  calc
    A x i = ((LinearMap.toMatrix' A.toLinearMap) *ᵥ x) i :=
      (congrFun (LinearMap.toMatrix'_mulVec A.toLinearMap x) i).symm
    _ = x i := lower_triangular_horizontal_mulVec _ hA hblock x i hi

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_vertical_covolume_lower
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 0 < scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) :
    let Λ := euclideanDerivativeLattice T hT scale (fun j => (hscale j).ne') Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let k := Module.finrank ℝ V
    ∃ p : Fin k → Fin m, Function.Injective p ∧
      1 / (l : ℝ) ^ k * (∏ i, scale (p i)) ≤
        ZLattice.covolume (latticeKernel (shortVectorLattice Λ R) π)
          (MeasureTheory.volume (α := V)) := by
  let Λ := euclideanDerivativeLattice T hT scale (fun j => (hscale j).ne') Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let : IsZLattice ℝ L :=
    euclideanDerivative_vertical_lattice_full T hT scale (fun j => (hscale j).ne') Y A l hl R
  let b := finiteLatticeBasis L
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  let v := fun j => f (b j).val
  have hli : LinearIndependent ℝ v := by
    have h := (b.ofZLatticeBasis ℝ L).linearIndependent.map' f.toLinearMap
      (LinearMap.ker_eq_bot.mpr f.injective)
    simpa only [v, Function.comp_def, Module.Basis.ofZLatticeBasis_apply,
      LinearIsometry.coe_toLinearMap] using h
  have hv (j) : v j ∈ Λ := (b j).property
  have hz (j) : euclideanDerivativeShiftMap T hT (v j) = 0 := (b j).val.property
  obtain ⟨B, hB, hgrid, he⟩ := exists_vertical_derivative_grid_matrix
    T hT scale (fun j => (hscale j).ne') Y A l hl v hli hv hz
  apply weighted_isometric_lattice_covolume_lower L b f Sum.inr Sum.inr_injective
    B hB l hl hgrid (LinearMap.toMatrix' A.toLinearMap) hA hdiag scale hscale
  intro j i
  have hc := congrArg (fun x : EuclideanSpace ℝ (σ ⊕ Fin m) => x (Sum.inr i)) (he j)
  change f (b j).val (Sum.inr i) = scale i * _
  rw [hc, euclideanVerticalMap_apply_inr]
  apply congrArg (fun t : ℝ => scale i * t)
  have hm := congrFun (LinearMap.toMatrix'_mulVec A.toLinearMap (B.col j)) i
  exact hm.symm

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_vertical_minor_data
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 0 < scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) :
    let Λ := euclideanDerivativeLattice T hT scale (fun j => (hscale j).ne') Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let k := Module.finrank ℝ V
    ∃ b : Module.Basis (Fin k) ℤ L, ∃ B : Matrix (Fin m) (Fin k) ℝ,
      LinearIndependent ℝ B.col ∧ (∀ j, B.col j ∈ realDenominatorGrid l) ∧
      (∀ j, (b j).val.val.val = euclideanVerticalMap scale (fun j => (hscale j).ne') A (B.col j)) ∧
      ∃ p : Fin k → Fin m, Function.Injective p ∧ (B.submatrix p id).det ≠ 0 ∧
        1 / (l : ℝ) ^ k * (∏ i, scale (p i)) ≤
          ZLattice.covolume L (MeasureTheory.volume (α := V)) := by
  let Λ := euclideanDerivativeLattice T hT scale (fun j => (hscale j).ne') Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let : IsZLattice ℝ L :=
    euclideanDerivative_vertical_lattice_full T hT scale (fun j => (hscale j).ne') Y A l hl R
  obtain ⟨b, B, hB, hgrid, he⟩ := exists_derivative_vertical_basis_matrix
    T hT scale (fun j => (hscale j).ne') Y A l hl R
  refine ⟨b, B, hB, hgrid, he, ?_⟩
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  apply weighted_isometric_lattice_minor_data L b f Sum.inr Sum.inr_injective
    B hB l hl hgrid (LinearMap.toMatrix' A.toLinearMap) hA hdiag scale hscale
  intro j i
  have hc := congrArg (fun x : EuclideanSpace ℝ (σ ⊕ Fin m) => x (Sum.inr i)) (he j)
  change (b j).val.val.val (Sum.inr i) = scale i * _
  rw [hc, euclideanVerticalMap_apply_inr]
  apply congrArg (fun t : ℝ => scale i * t)
  exact (congrFun (LinearMap.toMatrix'_mulVec A.toLinearMap (B.col j)) i).symm

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_horizontal_basis_data
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let k := Module.finrank ℝ V
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
    ∃ b : Module.Basis (Fin k) ℤ L, ∃ B : Matrix (Fin m) (Fin k) ℝ,
      LinearIndependent ℝ B.col ∧ (∀ j, B.col j ∈ realDenominatorGrid l) ∧
      (∀ j, (b j).val.val.val = euclideanVerticalMap scale hs0 A (B.col j)) ∧
      ∃ p : Fin k → Fin a, Function.Injective p ∧
        (B.submatrix (Fin.castLE ha ∘ p) id).det ≠ 0 := by
  let hspos : ∀ j, 0 < scale j := fun j => lt_of_lt_of_le zero_lt_one (hscale j)
  let Λ := euclideanDerivativeLattice T hT scale (fun j => (hspos j).ne') Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  dsimp only
  intro hupper
  obtain ⟨b, B, hB, hgrid, hrep, p, hp, hdet, hlower⟩ :=
    euclideanDerivative_vertical_minor_data T hT scale hspos Y A hA hdiag l hl R
  have hhor := pivots_lt_of_weighted_bound p hp scale hscale l hl a Tmin C _ hfar hlower hupper hlarge
  let q : Fin (Module.finrank ℝ V) → Fin a := fun i => ⟨(p i).val, hhor i⟩
  have hq (i) : Fin.castLE ha (q i) = p i := Fin.ext rfl
  refine ⟨b, B, hB, hgrid, hrep, q, ?_, ?_⟩
  · intro i j hij
    apply hp
    rw [← hq i, ← hq j, hij]
  · have he : Fin.castLE ha ∘ q = p := funext hq
    simpa only [he] using hdet

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_horizontal_injective
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
      Function.Injective ((euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)) := by
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  dsimp only
  intro hupper
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hs0 Y A l hl R
  obtain ⟨b, B, _, _, hrep, p, _, hdet⟩ := euclideanDerivative_horizontal_basis_data
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hfar hlarge hupper
  let bR := b.ofZLatticeBasis ℝ L
  have hcoord (j) (i : Fin a) : P (bR j) i = B (Fin.castLE ha i) j := by
    simp only [bR, Module.Basis.ofZLatticeBasis_apply]
    change (b j).val.val.val (Sum.inr (Fin.castLE ha i)) = B (Fin.castLE ha i) j
    rw [hrep]
    exact euclideanVerticalMap_horizontal scale hs0 hscalehor A hA hblock (B.col j)
      (Fin.castLE ha i) i.isLt
  apply basis_projection_injective_of_minor bR P p
  have he : Matrix.of (fun i j => P (bR j) (p i)) = B.submatrix (Fin.castLE ha ∘ p) id := by
    ext i j
    exact hcoord j (p i)
  rw [he]
  exact hdet

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_covolume_factorization
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → κ → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hscale Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let I := (latticeImage (shortVectorLattice Λ ρ) π).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup
    0 < I ∧ ∃ G : (σ → ℝ) →ₗ[ℝ] Z,
      (∀ y i, (G y).val (Sum.inl i) = y i) ∧
      (∀ x : Z, G (fun i => x.val (Sum.inl i)) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume (shortVectorLattice Λ ρ) =
        ZLattice.covolume (latticeKernel (shortVectorLattice Λ ρ) π)
          (MeasureTheory.volume (α := LinearMap.ker π)) *
          ((I : ℝ) / ∏ i, T i) *
          Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det := by
  let hTpos : ∀ i, 0 < T i := fun i => lt_of_lt_of_le zero_lt_one (hT i)
  let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T (fun i => (hTpos i).ne') scale hscale Y A l hl
  let Z := shortVectorSpan Λ ρ
  let π := (euclideanDerivativeShiftMap T (fun i => (hTpos i).ne')).comp Z.subtype
  have hproj := euclideanDerivativeLattice_shortSpan_projection
    T hT scale hscale Y A l hl R δ hR H r hr hnorm hdense hlarge
  have hsurj : Function.Surjective π :=
    euclidean_shift_subspace_surjective Z T (fun i => (hTpos i).ne') hproj
  have hinteger : ∀ x ∈ shortVectorLattice Λ ρ, π x ∈ realIntegerGrid := by
    intro x hx
    exact euclideanDerivativeShiftMap_integer T (fun i => (hTpos i).ne')
      scale hscale Y A l hl x.val hx
  exact ⟨latticeImage_index_pos _ π hinteger hsurj,
    exists_euclidean_lattice_graph_identity Z (shortVectorLattice Λ ρ) T hTpos hinteger hsurj⟩

end Erdos3

end

section

namespace Erdos3

theorem scaled_covolume_product_le {z k I E t C δ : ℝ} (ht : 0 < t) (hδ : 0 < δ)
    (hfactor : z = k * (I / t) * E) (hbound : z ≤ C / (δ * t)) :
    k * I * E ≤ C / δ := by
  calc
    k * I * E = z * t := by rw [hfactor]; field_simp [ht.ne']
    _ ≤ C / (δ * t) * t := mul_le_mul_of_nonneg_right hbound ht.le
    _ = C / δ := by field_simp

open Module

theorem euclideanDerivative_covolume_product_bound
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → κ → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let ρ := ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hscale Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let I := (latticeImage (shortVectorLattice Λ ρ) π).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup
    0 < I ∧ ∃ G : (σ → ℝ) →ₗ[ℝ] Z,
      (∀ y i, (G y).val (Sum.inl i) = y i) ∧
      (∀ x : Z, G (fun i => x.val (Sum.inl i)) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume (latticeKernel (shortVectorLattice Λ ρ) π)
        (MeasureTheory.volume (α := LinearMap.ker π)) * (I : ℝ) *
        Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det ≤
        (((finrank ℝ Z : ℝ) + 2) * ρ) ^ finrank ℝ Z / δ := by
  obtain ⟨hI, G, hG, hsection, hfactor⟩ := euclideanDerivative_covolume_factorization
    T hT scale hscale Y A l hl R δ hR H r hr hnorm hdense hlarge
  refine ⟨hI, G, hG, hsection, ?_⟩
  have hTpos (i) : 0 < T i := lt_of_lt_of_le zero_lt_one (hT i)
  have hbound := euclideanDerivative_covolume_density_bound T hTpos scale hscale
    Y A l hl R δ (zero_le_one.trans hR) hδ H r hr hnorm hdense
  exact scaled_covolume_product_le (Finset.prod_pos (fun i _ => hTpos i)) hδ hfactor hbound

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_index_graph_bounds
    {σ : Type*} [Fintype σ] [DecidableEq σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → Fin m → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i) :
    let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
    let Λ := euclideanDerivativeLattice T hT0 scale hs0 Y A l hl
    let Z := shortVectorSpan Λ ρ
    let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
    let k := Module.finrank ℝ (LinearMap.ker π)
    let I := (latticeImage (shortVectorLattice Λ ρ) π).toAddSubgroup.relIndex
      integerCoordinateLattice.toAddSubgroup
    let C := (((Module.finrank ℝ Z : ℝ) + 2) * ρ) ^ Module.finrank ℝ Z / δ
    0 < I ∧ ∃ G : (σ → ℝ) →ₗ[ℝ] Z,
      (∀ y i, (G y).val (Sum.inl i) = y i) ∧
      (∀ x : Z, G (fun i => x.val (Sum.inl i)) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume (latticeKernel (shortVectorLattice Λ ρ) π)
        (MeasureTheory.volume (α := LinearMap.ker π)) ≤ C ∧
      (I : ℝ) ≤ C * (l : ℝ) ^ k ∧
      Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ σ i))).det ≤ C * (l : ℝ) ^ k := by
  let hT0 : ∀ i, T i ≠ 0 := fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne'
  let hspos : ∀ j, 0 < scale j := fun j => lt_of_lt_of_le zero_lt_one (hscale j)
  let ρ := ((Fintype.card σ + Fintype.card (Fin m) : ℕ) : ℝ) * R
  let Λ := euclideanDerivativeLattice T hT0 scale (fun j => (hspos j).ne') Y A l hl
  let Z := shortVectorSpan Λ ρ
  let π := (euclideanDerivativeShiftMap T hT0).comp Z.subtype
  let k := Module.finrank ℝ (LinearMap.ker π)
  have hresult := euclideanDerivative_covolume_product_bound
    T hT scale (fun j => (hspos j).ne') Y A l hl R δ hR hδ H r hr hnorm hdense hlarge
  obtain ⟨hI, G, hG, hsection, hprod⟩ := hresult
  refine ⟨hI, G, hG, hsection, ?_⟩
  obtain ⟨p, _, hp⟩ := euclideanDerivative_vertical_covolume_lower
    T hT0 scale hspos Y A hA hdiag l hl ρ
  have hden : 0 < (l : ℝ) ^ k := pow_pos (by exact_mod_cast hl) _
  have hweights : 1 ≤ ∏ i, scale (p i) := Finset.one_le_prod₀ (fun i _ => hscale (p i))
  have hlower : 1 / (l : ℝ) ^ k ≤
      ZLattice.covolume (latticeKernel (shortVectorLattice Λ ρ) π)
        (MeasureTheory.volume (α := LinearMap.ker π)) := by
    calc
      1 / (l : ℝ) ^ k = 1 / (l : ℝ) ^ k * 1 := (mul_one _).symm
      _ ≤ 1 / (l : ℝ) ^ k * (∏ i, scale (p i)) :=
        mul_le_mul_of_nonneg_left hweights (one_div_pos.mpr hden).le
      _ ≤ _ := hp
  apply covolume_index_graph_bounds hden hlower
    (by exact_mod_cast Nat.succ_le_iff.mpr hI)
    (one_le_euclidean_section_gram_sqrt Z G hG)
  exact hprod

end Erdos3

end

end OAI
