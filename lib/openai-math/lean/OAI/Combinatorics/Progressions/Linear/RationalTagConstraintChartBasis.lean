import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.MvPolynomial.Basic
import OAI.Combinatorics.Progressions.Estimates.DerivativeIndexBounds
import OAI.Combinatorics.Progressions.Estimates.IndependentColumnsMinor
import OAI.Combinatorics.Progressions.Estimates.PartiallyBoundedNormalization
import OAI.Combinatorics.Progressions.Lattices.LatticeMinorNormBound
import OAI.Combinatorics.Progressions.Linear.RationalTagConstraintBasis
import OAI.Combinatorics.Progressions.Linear.TaggedSubmoduleBasis

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {κ V : Type*} [AddCommGroup V] [Module ℚ V]
  (K : Submodule ℚ V) (b : Basis κ ℚ K)

noncomputable def realSubmoduleBasis : Basis κ ℝ (K.baseChange ℝ) :=
  (b.baseChange ℝ).map (realificationSubmoduleEquiv K)

theorem realSubmoduleBasis_coe (i : κ) :
    (realSubmoduleBasis K b i : ℝ ⊗[ℚ] V) = (1 : ℝ) ⊗ₜ[ℚ] (b i : V) := by
  rw [realSubmoduleBasis, Basis.map_apply, Basis.baseChange_apply, realificationSubmoduleEquiv_tmul]

variable [Fintype κ]

noncomputable def realSubmoduleParameterization : (κ → ℝ) ≃ₗ[ℝ] K.baseChange ℝ :=
  (realSubmoduleBasis K b).equivFun.symm

theorem realSubmoduleParameterization_basis (i : κ) :
    realSubmoduleParameterization K b (Pi.basisFun ℝ κ i) = realSubmoduleBasis K b i := by
  classical
  apply (realSubmoduleBasis K b).equivFun.injective
  rw [realSubmoduleParameterization, LinearEquiv.apply_symm_apply]
  ext j
  simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]

end Erdos3

end

section

namespace Erdos3

theorem exists_rational_matrix_of_grid_columns {ι κ : Type*}
    (B : Matrix ι κ ℝ) (l : ℕ) (hl : 0 < l)
    (hB : ∀ j, B.col j ∈ realDenominatorGrid l) :
    ∃ Q : Matrix ι κ ℚ, (∀ j, Q.col j ∈ denominatorGrid l) ∧
      ∀ j, (fun i => (Q i j : ℝ)) = B.col j := by
  choose q hq he using fun j => realDenominatorGrid_exists_rational l hl (B.col j) (hB j)
  exact ⟨fun i j => q j i, hq, he⟩

theorem basis_projection_range_eq_span {E ι κ : Type*}
    [AddCommGroup E] [Module ℝ E] (b : Module.Basis κ ℝ E)
    (P : E →ₗ[ℝ] (ι → ℝ)) :
    LinearMap.range P = Submodule.span ℝ (Set.range (fun j => P (b j))) := by
  rw [← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp]
  rfl

theorem exists_rational_basis_projection {E ι κ : Type*}
    [AddCommGroup E] [Module ℝ E] (b : Module.Basis κ ℝ E)
    (P : E →ₗ[ℝ] (ι → ℝ)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, P (b j) ∈ realDenominatorGrid l) :
    ∃ Q : Matrix ι κ ℚ, (∀ j, Q.col j ∈ denominatorGrid l) ∧
      (∀ j, (fun i => (Q i j : ℝ)) = P (b j)) ∧
      LinearMap.range P = Submodule.span ℝ (Set.range (fun j => fun i => (Q i j : ℝ))) := by
  obtain ⟨Q, hQ, he⟩ := exists_rational_matrix_of_grid_columns
    (Matrix.of (fun i j => P (b j) i)) l hl hgrid
  refine ⟨Q, hQ, he, ?_⟩
  rw [basis_projection_range_eq_span b P]
  congr 2
  funext j
  exact (he j).symm

end Erdos3

end

section

namespace Erdos3

theorem exists_bounded_normalized_rational_image_basis {E ι : Type*} {k : ℕ}
    [AddCommGroup E] [Module ℝ E]
    (b : Module.Basis (Fin k) ℝ E) (P : E →ₗ[ℝ] (ι → ℝ))
    (l : ℕ) (hl : 0 < l) (hgrid : ∀ j, P (b j) ∈ realDenominatorGrid l)
    (p : Fin k → ι) (hp : (Matrix.of (fun i j => P (b j) (p i))).det ≠ 0)
    (C : ℝ) (hminor : ∀ q : Fin k → ι, |(Matrix.of (fun i j => P (b j) (q i))).det| ≤ C) :
    ∃ Q : Matrix ι (Fin k) ℚ,
      LinearIndependent ℚ Q.col ∧ LinearIndependent ℝ (Q.map (Rat.castHom ℝ)).col ∧
      (∀ i j, RationalHeightLE (Q i j) (Nat.ceil (C * (l : ℝ) ^ k))) ∧
      LinearMap.range P = Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col) := by
  let H := Matrix.of (fun i j => P (b j) i)
  obtain ⟨Q, hQ, hheight, hidentity⟩ :=
    exists_bounded_rational_row_normalization H l hl hgrid p hp C hminor
  have hrealidentity : (Q.map (Rat.castHom ℝ)).submatrix p id = 1 := by
    have h := congrArg (fun M : Matrix (Fin k) (Fin k) ℚ => M.map (Rat.castHom ℝ)) hidentity
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at h
    calc
      _ = (Q.submatrix p id).map (Rat.castHom ℝ) := rfl
      _ = 1 := h
  refine ⟨Q, independent_columns_of_identity_minor Q p hidentity,
    independent_columns_of_identity_minor _ p hrealidentity, hheight, ?_⟩
  rw [hQ, row_normalization_col_span H p hp]
  exact basis_projection_range_eq_span b P

end Erdos3

end

section

namespace Erdos3

theorem exists_bounded_rational_projection_lift
    {E F α β : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype α] {k : ℕ}
    (b : Module.Basis (Fin k) ℝ E) (P : E →ₗ[ℝ] (α → ℝ))
    (hP : Function.Injective P) (g : E →ₗ[ℝ] (β → ℝ))
    (e : α → β) (hhor : ∀ v i, g v (e i) = P v i)
    (W : (β → ℝ) →ₗ[ℝ] F) (C : ℝ)
    (hbound : ∀ v, ‖W (g v)‖ ≤ C * ‖P v‖)
    (B : Matrix β (Fin k) ℝ) (hB : ∀ i j, B i j = g (b j) i)
    (p : Fin k → α) (hp : (B.submatrix (e ∘ p) id).det ≠ 0)
    (Q : Matrix β (Fin k) ℚ)
    (hQ : Q.map (Rat.castHom ℝ) = B * (B.submatrix (e ∘ p) id)⁻¹)
    (hQid : Q.submatrix (e ∘ p) id = 1) :
    let QH := Q.submatrix e id
    ∃ R : LinearMap.range P →ₗ[ℝ] (β → ℝ),
      (∀ x i, R x (e i) = x.val i) ∧
      (∀ x, ‖W (R x)‖ ≤ C * ‖x‖) ∧
      (∀ v, R ⟨P v, v, rfl⟩ = g v) ∧
      LinearMap.range P = Submodule.span ℝ (Set.range (QH.map (Rat.castHom ℝ)).col) ∧
      LinearIndependent ℝ (QH.map (Rat.castHom ℝ)).col ∧
      LinearIndependent ℚ QH.col ∧
      (∀ j, ∃ x : LinearMap.range P,
        x.val = (QH.map (Rat.castHom ℝ)).col j ∧ R x = (Q.map (Rat.castHom ℝ)).col j) := by
  let J := (LinearEquiv.ofInjective P hP).symm.toLinearMap
  have hJ (x : LinearMap.range P) : P (J x) = x.val :=
    congrArg Subtype.val ((LinearEquiv.ofInjective P hP).apply_symm_apply x)
  let R := g.comp J
  let H := B.submatrix e id
  let QH := Q.submatrix e id
  have hHcol : H.col = fun j => P (b j) := by
    funext j i
    exact (hB (e i) j).trans (hhor (b j) i)
  have hQH : QH.map (Rat.castHom ℝ) = H * (H.submatrix p id)⁻¹ := by
    ext i j
    exact congrArg (fun M : Matrix β (Fin k) ℝ => M (e i) j) hQ
  have hQHid : QH.submatrix p id = 1 := hQid
  have hrealid : (QH.map (Rat.castHom ℝ)).submatrix p id = 1 := by
    rw [hQH]
    exact row_normalization_submatrix H p hp
  refine ⟨R, ?_, ?_, ?_, ?_, independent_columns_of_identity_minor _ p hrealid,
    independent_columns_of_identity_minor QH p hQHid, ?_⟩
  · intro x i
    exact (hhor (J x) i).trans (congrFun (hJ x) i)
  · intro x
    have h := hbound (J x)
    rw [hJ x] at h
    exact h
  · intro v
    have h : J ⟨P v, v, rfl⟩ = v := hP (hJ ⟨P v, v, rfl⟩)
    change g (J ⟨P v, v, rfl⟩) = g v
    rw [h]
  · change LinearMap.range P = Submodule.span ℝ (Set.range (QH.map (Rat.castHom ℝ)).col)
    rw [hQH, row_normalization_col_span H p hp, hHcol]
    exact basis_projection_range_eq_span b P
  · intro j
    obtain ⟨v, hv⟩ := exists_normalized_basis_vector b g B hB
      (B.submatrix (e ∘ p) id)⁻¹ j
    have hv' : g v = (Q.map (Rat.castHom ℝ)).col j := by
      rw [hQ]
      exact hv
    let x : LinearMap.range P := ⟨P v, v, rfl⟩
    refine ⟨x, ?_, ?_⟩
    · funext i
      exact (hhor v i).symm.trans (congrFun hv' (e i))
    · have hx : J x = v := hP (hJ x)
      change g (J x) = _
      rw [hx]
      exact hv'

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
  (e : Basis ι ℚ V) (K : Submodule ℚ V) (b : Basis κ ℚ K)

noncomputable def submoduleBasisMatrix : Matrix ι κ ℚ :=
  fun i j => e.repr (b j).val i

theorem realSubmoduleBasis_matrix_coordinates (j : κ) :
    (e.baseChange ℝ).equivFun (realSubmoduleBasis K b j).val =
      ((submoduleBasisMatrix e K b).map (Rat.castHom ℝ)).col j := by
  funext i
  rw [Basis.equivFun_apply, realSubmoduleBasis_coe, Basis.baseChange_repr_tmul]
  simp [submoduleBasisMatrix, Matrix.col, Algebra.smul_def]

theorem realSubmoduleBasis_matrix_span :
    Submodule.span ℝ (Set.range ((submoduleBasisMatrix e K b).map (Rat.castHom ℝ)).col) =
      (K.baseChange ℝ).map (e.baseChange ℝ).equivFun.toLinearMap := by
  let f := (e.baseChange ℝ).equivFun.toLinearMap.comp (K.baseChange ℝ).subtype
  have he : (f ∘ realSubmoduleBasis K b) =
      ((submoduleBasisMatrix e K b).map (Rat.castHom ℝ)).col := by
    funext j
    exact realSubmoduleBasis_matrix_coordinates e K b j
  have hs := congrArg (fun U : Submodule ℝ (K.baseChange ℝ) => U.map f)
    (realSubmoduleBasis K b).span_eq
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, he] at hs
  exact hs.trans (by simp only [f, LinearMap.range_comp, Submodule.range_subtype])

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {B I : Type*} [Fintype B]
  (U : Submodule ℚ (B → ℚ)) (b : Basis I ℚ U)

noncomputable def rationalCoordinateRealBasis : Basis I ℝ (realRationalCoordinateSpan U) :=
  (realSubmoduleBasis U b).map (realRationalCoordinateEquiv.submoduleMap (U.baseChange ℝ))

@[simp] theorem rationalCoordinateRealBasis_apply (i : I) (j : B) :
    (rationalCoordinateRealBasis U b i : B → ℝ) j = ((b i : B → ℚ) j : ℝ) := by
  change realRationalCoordinateEquiv (realSubmoduleBasis U b i : ℝ ⊗[ℚ] (B → ℚ)) j = _
  rw [realSubmoduleBasis_coe, realRationalCoordinateEquiv_tmul, one_mul]

theorem realRationalCoordinateSpan_basis :
    Submodule.span ℝ (Set.range (fun i j => ((b i : B → ℚ) j : ℝ))) =
      realRationalCoordinateSpan U := by
  have hb : Submodule.span ℚ (Set.range (fun i => (b i : B → ℚ))) = U := by
    change Submodule.span ℚ (Set.range (U.subtype ∘ b)) = U
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  exact (realRationalCoordinateSpan_span (fun i => (b i : B → ℚ))).symm.trans
    (congrArg realRationalCoordinateSpan hb)

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_bounded_horizontal_basis
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
    let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
    let k := Module.finrank ℝ V
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
      Function.Injective P ∧ ∃ Q : Matrix (Fin a) (Fin k) ℚ,
        LinearIndependent ℚ Q.col ∧ LinearIndependent ℝ (Q.map (Rat.castHom ℝ)).col ∧
        (∀ i j, RationalHeightLE (Q i j) (Nat.ceil (C * (l : ℝ) ^ k))) ∧
        LinearMap.range P = Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col) := by
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  dsimp only
  intro hupper
  have hinj : Function.Injective P := euclideanDerivative_horizontal_injective
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hscalehor hblock hfar hlarge hupper
  refine ⟨hinj, ?_⟩
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hs0 Y A l hl R
  obtain ⟨b, B, _, hgrid, hrep, p, _, hdet⟩ := euclideanDerivative_horizontal_basis_data
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hfar hlarge hupper
  let bR := b.ofZLatticeBasis ℝ L
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  let e : Fin a → σ ⊕ Fin m := fun i => Sum.inr (Fin.castLE ha i)
  have he : Function.Injective e := by
    intro i j hij
    have h : Fin.castLE ha i = Fin.castLE ha j := Sum.inr.inj hij
    exact Fin.ext (congrArg (fun u : Fin m => u.val) h)
  have hcoord (j) (i : Fin a) : P (bR j) i = B (Fin.castLE ha i) j := by
    simp only [bR, Module.Basis.ofZLatticeBasis_apply]
    change (b j).val.val.val (Sum.inr (Fin.castLE ha i)) = B (Fin.castLE ha i) j
    rw [hrep]
    exact euclideanVerticalMap_horizontal scale hs0 hscalehor A hA hblock (B.col j)
      (Fin.castLE ha i) i.isLt
  have hPgrid (j) : P (bR j) ∈ realDenominatorGrid l := by
    obtain ⟨z, hz⟩ := hgrid j
    refine ⟨fun i => z (Fin.castLE ha i), ?_⟩
    funext i
    change (z (Fin.castLE ha i) : ℝ) = (l : ℝ) * P (bR j) i
    rw [hcoord]
    exact congrFun hz (Fin.castLE ha i)
  have hp : (Matrix.of (fun i j => P (bR j) (p i))).det ≠ 0 := by
    have hm : Matrix.of (fun i j => P (bR j) (p i)) = B.submatrix (Fin.castLE ha ∘ p) id := by
      ext i j
      exact hcoord j (p i)
    rw [hm]
    exact hdet
  apply exists_bounded_normalized_rational_image_basis bR P l hl hPgrid p hp C
  let H := Matrix.of (fun i j => P (bR j) i)
  have hH (i j) : H i j = f (b j).val (e i) := by
    simp only [H, Matrix.of_apply, bR, Module.Basis.ofZLatticeBasis_apply]
    rfl
  intro q
  exact (lattice_projection_all_minors_bound L b f e he H hH q).trans hupper

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_rational_lift_matrix_data
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
    let k := Module.finrank ℝ V
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
      ∃ b : Module.Basis (Fin k) ℤ L, ∃ B : Matrix (Fin m) (Fin k) ℝ,
        ∃ p : Fin k → Fin a,
          (∀ j, B.col j ∈ realDenominatorGrid l) ∧
          (∀ j, (b j).val.val.val = euclideanVerticalMap scale hs0 A (B.col j)) ∧
          (B.submatrix (Fin.castLE ha ∘ p) id).det ≠ 0 ∧
          ∃ D : ℕ, 0 < D ∧ D ≤ Nat.ceil (C * (l : ℝ) ^ k) ∧
            ∃ Q : Matrix (Fin m) (Fin k) ℚ,
              (∀ j, Q.col j ∈ denominatorGrid D) ∧
              Q.map (Rat.castHom ℝ) = B * (B.submatrix (Fin.castLE ha ∘ p) id)⁻¹ ∧
              Q.submatrix (Fin.castLE ha ∘ p) id = 1 ∧
              (∀ i j, RationalHeightLE (Q (Fin.castLE ha i) j)
                (Nat.ceil (C * (l : ℝ) ^ k))) := by
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  dsimp only
  intro hupper
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hs0 Y A l hl R
  obtain ⟨b, B, _, hgrid, hrep, p, _, hdet⟩ := euclideanDerivative_horizontal_basis_data
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hfar hlarge hupper
  refine ⟨b, B, p, hgrid, hrep, hdet, ?_⟩
  apply exists_partially_bounded_grid_normalization B l hl hgrid (Fin.castLE ha) p hdet C
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  let e : Fin a → σ ⊕ Fin m := fun i => Sum.inr (Fin.castLE ha i)
  have he : Function.Injective e := by
    intro i j hij
    have h : Fin.castLE ha i = Fin.castLE ha j := Sum.inr.inj hij
    exact Fin.ext (congrArg (fun u : Fin m => u.val) h)
  let H := B.submatrix (Fin.castLE ha) id
  have hH (i j) : H i j = f (b j).val (e i) := by
    change B (Fin.castLE ha i) j = (b j).val.val.val (Sum.inr (Fin.castLE ha i))
    rw [hrep]
    exact (euclideanVerticalMap_horizontal scale hs0 hscalehor A hA hblock (B.col j)
      (Fin.castLE ha i) i.isLt).symm
  intro q
  exact (lattice_projection_all_minors_bound L b f e he H hH q).trans hupper

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {J : Fin m → Type*}

noncomputable def rationalTagChartMatrix
    (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (W j)) :
    (Σ j, Fin (n j)) → (Σ j, J j) → ℚ :=
  fun a x => (Pi.single (M := fun j => J j → ℚ) a.1
    (b a.1 a.2 : J a.1 → ℚ)) x.1 x.2

theorem rationalTagChartMatrix_same
    (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (W j)) (j : Fin m) (a : Fin (n j)) (i : J j) :
    rationalTagChartMatrix W n b ⟨j, a⟩ ⟨j, i⟩ = (b j a : J j → ℚ) i := by
  simp [rationalTagChartMatrix]

theorem rationalTagChartMatrix_of_ne
    (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (W j)) (a : Σ j, Fin (n j)) (x : Σ j, J j)
    (h : x.1 ≠ a.1) : rationalTagChartMatrix W n b a x = 0 := by
  simp [rationalTagChartMatrix, Pi.single_eq_of_ne h]

theorem rationalTagChartMatrix_height
    (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (W j)) {P : ℝ} (hP : 0 ≤ P)
    (hb : ∀ j a i, rationalLogHeight ((b j a : J j → ℚ) i) ≤ P) :
    ∀ a x, rationalLogHeight (rationalTagChartMatrix W n b a x) ≤ P := by
  rintro ⟨j, a⟩ ⟨k, i⟩
  by_cases h : k = j
  · subst k
    rw [rationalTagChartMatrix_same]
    exact hb j a i
  · rw [rationalTagChartMatrix_of_ne W n b ⟨j, a⟩ ⟨k, i⟩ h]
    simpa [rationalLogHeight] using hP

theorem RationalTaggedConstraintCertificate.exists_bounded_chart_tag_basis {X : Type*}
    [∀ j, Fintype (J j)]
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ K p Cblocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    ∃ (n : Fin m → ℕ) (Ktag : Submodule ℝ ((Σ j, J j) → ℝ))
      (b : Basis (Σ j, Fin (n j)) ℝ Ktag)
      (matrix : (Σ j, Fin (n j)) → (Σ j, J j) → ℚ),
      (∀ j, n j ≤ Fintype.card (J j)) ∧
      (∀ a x, (b a : (Σ j, J j) → ℝ) x = (matrix a x : ℝ)) ∧
      (∀ a x, x.1 ≠ a.1 → matrix a x = 0) ∧
      (∀ a x, rationalLogHeight (matrix a x) ≤ ((p + 2) ^ 2 + 2) ^ 63) ∧
      K = {point | (fun x => point (Sum.inr x)) ∈ Ktag} ∧
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ)),
        (∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ U j) → point ∈ K) →
        ∀ v : (Σ j, J j) → ℝ, (∀ j, (fun i => v ⟨j, i⟩) ∈ U j) → v ∈ Ktag := by
  classical
  obtain ⟨W, n, b, hn, hb, hK⟩ := hcert.exists_bounded_tag_bases_univ hp hdim hblocks
  let R := fun j => realRationalCoordinateSpan (W j)
  let br := fun j => rationalCoordinateRealBasis (W j) (b j)
  let Ktag := taggedSubmodule R
  let basis : Basis (Σ j, Fin (n j)) ℝ Ktag := taggedSubmoduleBasis R br
  let matrix := rationalTagChartMatrix W n b
  have hentry (a : Σ j, Fin (n j)) (x : Σ j, J j) :
      (basis a : (Σ j, J j) → ℝ) x = (matrix a x : ℝ) := by
    rcases a with ⟨j, a⟩
    rcases x with ⟨k, i⟩
    by_cases h : k = j
    · subst k
      change ((taggedSubmoduleBasis R br ⟨j, a⟩ : (Σ j, J j) → ℝ) ⟨j, i⟩) = _
      rw [taggedSubmoduleBasis_same]
      dsimp only [matrix]
      rw [rationalTagChartMatrix_same]
      exact rationalCoordinateRealBasis_apply (W j) (b j) a i
    · rw [show (basis ⟨j, a⟩ : (Σ j, J j) → ℝ) ⟨k, i⟩ = 0 from
        taggedSubmoduleBasis_of_ne R br j a k i h]
      rw [show matrix ⟨j, a⟩ ⟨k, i⟩ = 0 from
        rationalTagChartMatrix_of_ne W n b ⟨j, a⟩ ⟨k, i⟩ h, Rat.cast_zero]
  have htag : K = {point | (fun x => point (Sum.inr x)) ∈ Ktag} := by
    rw [hK]
    ext point
    change (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈
      Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ)))) ↔
      ∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ realRationalCoordinateSpan (W j)
    simp_rw [realRationalCoordinateSpan_basis]
  refine ⟨n, Ktag, basis, matrix, hn, hentry,
    rationalTagChartMatrix_of_ne W n b,
    rationalTagChartMatrix_height W n b (by positivity) hb, htag, ?_⟩
  intro U hret v hv
  have hpoint := hret (Sum.elim (fun _ : X => (0 : ℝ)) v) (by simpa using hv)
  simpa only [htag, Set.mem_ofPred_eq, Sum.elim_inr] using hpoint

theorem retained_tag_polynomial_coefficients_mem {X V : Type*}
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (Ktag : Submodule ℝ ((Σ j, J j) → ℝ))
    (hK : K = {point | (fun x => point (Sum.inr x)) ∈ Ktag})
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hret : ∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ U j) → point ∈ K)
    (A : (Σ j, J j) → MvPolynomial V ℝ)
    (hA : ∀ α j, (fun i => (A ⟨j, i⟩).coeff α) ∈ U j) :
    ∀ α, (fun x => (A x).coeff α) ∈ Ktag := by
  intro α
  have h := hret (Sum.elim (fun _ : X => (0 : ℝ)) (fun x => (A x).coeff α))
    (by simpa using hA α)
  simpa only [hK, Set.mem_ofPred_eq, Sum.elim_inr] using h

end Erdos3.VectorPolynomial

end

end OAI
