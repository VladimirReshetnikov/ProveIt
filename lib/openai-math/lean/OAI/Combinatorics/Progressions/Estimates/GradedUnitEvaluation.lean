/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import OAI.Combinatorics.Progressions.Estimates.StrongRefiltrationReconstruction
import OAI.Combinatorics.Progressions.Polynomial.FirstCoefficientPolynomialDerivative

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

noncomputable def reducedSquareGradedSndMap :
    F.squareFiltration.quotientTop.AssociatedGraded →ₗ⁅ℚ⁆ F.quotientTop.AssociatedGraded :=
  F.squareFiltration.quotientTop.associatedGradedMap F.quotientTop
    F.reducedSquareSnd F.reducedSquareSnd_mem

noncomputable def fastGradedDiagonal
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    LieSubalgebra ℚ F.quotientTop.AssociatedGraded :=
  W.map F.reducedSquareGradedSndMap

noncomputable def fullFastGradedDiagonal
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    LieSubalgebra ℚ F.AssociatedGraded :=
  (F.fastGradedDiagonal W).comap F.quotientTopGradedMap

theorem fullFastGradedDiagonal_top
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) (x : F.layer (s + 1)) :
    F.associatedGradedPieceMap (s + 1) x ∈ F.fullFastGradedDiagonal W := by
  change F.quotientTopGradedMap (F.associatedGradedPieceMap (s + 1) x) ∈ F.fastGradedDiagonal W
  rw [F.quotientTopGradedMap_top]
  exact (F.fastGradedDiagonal W).zero_mem

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "ωQ" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))
local notation "bQ" => F.quotientTop.associatedGradedBasis
  (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)

noncomputable def fastPointwiseSquare (w : σ → ℕ)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w) :=
  F.squareFiltration.quotientTop.symbolPointwiseSubalgebra
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w W

theorem fastGradedDiagonal_graded
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    BasisGradedSubmodule bQ ωQ (F.fastGradedDiagonal W).toSubmodule :=
  F.squareFiltration.quotientTop.associatedGradedMap_image_graded F.quotientTop
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem W hW

theorem fullFastGradedDiagonal_graded
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω (F.fullFastGradedDiagonal W).toSubmodule :=
  F.associatedGradedMap_comap_graded F.quotientTop e ω hF
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    (lieQuotientMap (F.layerIdeal (s + 1))) (fun _ _ hx => F.quotientLie_mem _ le_rfl hx)
    (F.fastGradedDiagonal W) (F.fastGradedDiagonal_graded e ω hF W hW)

theorem fastPointwiseDiagonal_eq [Fintype σ] [Fintype ι] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W) =
      F.quotientTop.symbolPointwiseSubalgebra (F.quotientTopBasis e ω hF) ωQ
        (F.quotientTopBasis_layers e ω hF) w (F.fastGradedDiagonal W) := by
  let : Fintype (SymbolBasisIndex w ωQ) := symbolBasisIndexFintype w ωQ s hw
    (F.quotientTop.adaptedBasis_weight_le_step (F.quotientTopBasis e ω hF) ωQ
      (F.quotientTopBasis_layers e ω hF))
  exact F.squareFiltration.quotientTop.symbolPointwiseSubalgebra_map F.quotientTop
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w W hW

theorem fullFastPointwise_image_le [Fintype σ] [Fintype ι] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    (F.symbolPointwiseSubalgebra e ω hF w (F.fullFastGradedDiagonal W)).map (F.quotientTopSymbolMap w) ≤
      F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W) := by
  rw [F.fastPointwiseDiagonal_eq e ω hF w hw W hW]
  have hm := F.symbolPointwiseSubalgebra_map_le F.quotientTop e ω hF
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    (lieQuotientMap (F.layerIdeal (s + 1))) (fun _ _ hx => F.quotientLie_mem _ le_rfl hx)
    w (F.fullFastGradedDiagonal W)
  have hle : (F.fullFastGradedDiagonal W).map F.quotientTopGradedMap ≤ F.fastGradedDiagonal W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  exact hm.trans (F.quotientTop.symbolPointwiseSubalgebra_mono
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF) w hle)

theorem fullFastPointwise_subgroup_le [Fintype σ] [Fintype ι] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    F.realPointwisePolynomialSubgroup e ω hF w (F.fullFastGradedDiagonal W) ≤
      F.realFastDiagonalSubgroup w (F.fastPointwiseSquare e ω hF w W) :=
  F.realPointwisePolynomialSubgroup_le_fast e ω hF w (F.fullFastGradedDiagonal W)
    (F.fastPointwiseSquare e ω hF w W) (F.fullFastPointwise_image_le e ω hF w hw W hW)

theorem fullFastPointwise_eq_comap [Fintype σ] [Fintype ι] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    F.symbolPointwiseSubalgebra e ω hF w (F.fullFastGradedDiagonal W) =
      (F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W)).comap
        (F.quotientTopSymbolMap w) := by
  rw [F.fastPointwiseDiagonal_eq e ω hF w hw W hW]
  exact (F.symbolPointwiseSubalgebra_comap F.quotientTop e ω hF
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    (lieQuotientMap (F.layerIdeal (s + 1))) (fun _ _ hx => F.quotientLie_mem _ le_rfl hx)
    w (F.fastGradedDiagonal W)).symm

theorem fullFastPointwise_subgroup_eq [Fintype σ] [Fintype ι] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    F.realPointwisePolynomialSubgroup e ω hF w (F.fullFastGradedDiagonal W) =
      F.realFastDiagonalSubgroup w (F.fastPointwiseSquare e ω hF w W) := by
  ext g
  rw [F.mem_realPointwisePolynomialSubgroup, F.mem_realFastDiagonalSubgroup,
    F.adaptedReducedRealSymbolHom_coord]
  change F.realExtendedSymbolMap w g.coord ∈
      (F.symbolPointwiseSubalgebra e ω hF w (F.fullFastGradedDiagonal W)).toSubmodule.baseChange ℝ ↔
    (F.quotientTopSymbolMap w).toLinearMap.baseChange ℝ (F.realExtendedSymbolMap w g.coord) ∈
      (F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W)).toSubmodule.baseChange ℝ
  have he : (F.symbolPointwiseSubalgebra e ω hF w (F.fullFastGradedDiagonal W)).toSubmodule =
      (F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W)).toSubmodule.comap
        (F.quotientTopSymbolMap w).toLinearMap :=
    congrArg LieSubalgebra.toSubmodule (F.fullFastPointwise_eq_comap e ω hF w hw W hW)
  rw [he, realification_comap]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
  (hW : BasisGradedSubmodule
    (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))
    (fun i => squareBasisWeight ω i.val) W.toSubmodule)

include hW

theorem fullFast_horizontal_derivative_mem [DecidableEq σ]
    (B : F.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (hB : B ∈ F.realFastDiagonalSubgroup (fun _ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W))
    (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) B.coord) 0 = 0) (i : σ) :
    F.realFastCoefficientHorizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      (F.reducedSquareFastRelativeSubmodule (fun _ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W))
      (F.realFastCoefficientDirectionMap (F.fastPointwiseSquare e ω hF (fun _ => 1) W) B (Pi.single i 1)) ∈
      (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W)).baseChange ℝ := by
  have hb : B ∈ F.realPointwisePolynomialSubgroup e ω hF (fun _ => 1) (F.fullFastGradedDiagonal W) := by
    rw [F.fullFastPointwise_subgroup_eq e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) W hW]
    exact hB
  have hs := (F.mem_realPointwisePolynomialSubgroup e ω hF (fun _ => 1) (F.fullFastGradedDiagonal W) B).mp hb
  exact F.pointwise_horizontal_derivative_mem e ω hF (F.fullFastGradedDiagonal W) B.coord hs hzero i

theorem fullFast_horizontal_correction_mem
    (a : σ → ℝ ⊗[ℚ] (L ⧸ F.layer 2))
    (ha : ∀ i, a i ∈ (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W)).baseChange ℝ) :
    F.realLayerOneCorrection e ω hF a ∈ F.realFastDiagonalSubgroup (fun _ => 1)
      (F.fastPointwiseSquare e ω hF (fun _ => 1) W) :=
  F.fullFastPointwise_subgroup_le e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) W hW
    (F.realLayerOneCorrection_mem_pointwiseSubgroup e ω hF (F.fullFastGradedDiagonal W) a ha)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

section Projection

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem gradedPieceProjection_basis (j : ℕ) (i : ι) :
    F.gradedPieceProjection e ω hF j (e i) =
      if ω i = j then F.associatedGradedBasis e ω hF i else 0 := by
  classical
  apply (F.associatedGradedBasis e ω hF).repr.injective
  ext k
  rw [F.gradedPieceProjection_coordinate]
  by_cases hi : i = k <;> by_cases hj : ω i = j <;>
    simp_all only [Basis.repr_self, Finsupp.single_apply, ite_true, ite_false,
      map_zero, Finsupp.zero_apply, ite_self]

end Projection

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem reducedSquareDifference_basis (a : ReducedSquareBasisIndex s ω) :
    F.reducedSquareDifference (F.reducedSquareBasis e ω hF a) =
      Sum.elim (fun _ : ι => (0 : L)) (fun i : {i // 2 ≤ ω i} => e i.val) a.val := by
  dsimp only [reducedSquareBasis]
  rw [F.squareFiltration.quotientTopBasis_apply, F.reducedSquareDifference_mk]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl i => rw [F.adaptedSquareBasis_inl, sub_self]; rfl
  | inr i => rw [F.adaptedSquareBasis_inr, sub_zero]; rfl

noncomputable def reducedSquareGradedDifference :
    F.squareFiltration.quotientTop.AssociatedGraded →ₗ[ℚ] F.AssociatedGraded :=
  (bW).constr ℚ (fun a => Sum.elim (fun _ : ι => (0 : F.AssociatedGraded))
    (fun i : {i // 2 ≤ ω i} => F.associatedGradedBasis e ω hF i.val) a.val)

theorem reducedSquareGradedDifference_basis (a : ReducedSquareBasisIndex s ω) :
    F.reducedSquareGradedDifference e ω hF (bW a) =
      Sum.elim (fun _ : ι => (0 : F.AssociatedGraded))
        (fun i : {i // 2 ≤ ω i} => F.associatedGradedBasis e ω hF i.val) a.val := by
  exact Basis.constr_basis _ _ _ a

theorem reducedSquareGradedDifference_projection (j : ℕ)
    (x : F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) :
    F.reducedSquareGradedDifference e ω hF
        (F.squareFiltration.quotientTop.gradedPieceProjection
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) j x) =
      F.gradedPieceProjection e ω hF (j + 1) (F.reducedSquareDifference x) := by
  have he : (F.reducedSquareGradedDifference e ω hF).comp
      (F.squareFiltration.quotientTop.gradedPieceProjection
        (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) j) =
      (F.gradedPieceProjection e ω hF (j + 1)).comp F.reducedSquareDifference := by
    apply (F.reducedSquareBasis e ω hF).ext
    intro a
    simp only [LinearMap.comp_apply, F.squareFiltration.quotientTop.gradedPieceProjection_basis,
      F.reducedSquareDifference_basis]
    simp only [apply_ite, map_zero, F.reducedSquareGradedDifference_basis]
    rcases a with ⟨a, ha⟩
    cases a with
    | inl i => simp only [Sum.elim_inl, map_zero, ite_self]
    | inr i =>
      simp only [Sum.elim_inr, squareBasisWeight, F.gradedPieceProjection_basis]
      have hi : (ω i.val - 1 = j) ↔ ω i.val = j + 1 := by have h := i.property; omega
      simp only [hi]
  exact LinearMap.congr_fun he x

theorem reducedSquareGradedDifference_gradeProjection (j : ℕ)
    (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    F.reducedSquareGradedDifference e ω hF (basisGradeProjection bW ωW j x) =
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (j + 1)
        (F.reducedSquareGradedDifference e ω hF x) := by
  have he : (F.reducedSquareGradedDifference e ω hF).comp (basisGradeProjection bW ωW j) =
      (basisGradeProjection (F.associatedGradedBasis e ω hF) ω (j + 1)).comp
        (F.reducedSquareGradedDifference e ω hF) := by
    apply (bW).ext
    intro a
    simp only [LinearMap.comp_apply, basisGradeProjection, basisCoordinateProjection_basis,
      Set.mem_ofPred_eq]
    simp only [apply_ite, map_zero, F.reducedSquareGradedDifference_basis]
    rcases a with ⟨a, ha⟩
    cases a with
    | inl i => simp only [Sum.elim_inl, map_zero, ite_self]
    | inr i =>
      simp only [Sum.elim_inr, squareBasisWeight, basisCoordinateProjection_basis, Set.mem_ofPred_eq]
      have hi : (ω i.val - 1 = j) ↔ ω i.val = j + 1 := by have h := i.property; omega
      simp only [hi]
  exact LinearMap.congr_fun he x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))

theorem firstCoefficientGradedPolynomial_normalized (p : F.normalizedRelativeSubmodule w) :
    F.firstCoefficientGradedPolynomial e ω hF w (F.normalizedFirstCoefficientMap w p) =
      F.shiftedGradedPolynomial e ω hF w 1 p.val.val := by
  change F.firstCoefficientGradedPolynomial e ω hF w
    (F.firstCoefficientMap w ⟨p.val, p.property.1⟩) = _
  rw [F.firstCoefficientGradedPolynomial_map, F.adaptedShiftedGradedPolynomial_apply]

theorem firstCoefficientGradedPolynomial_reducedSquare_symbol
    (p : F.squareFiltration.quotientTop.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.firstCoefficientGradedPolynomial e ω hF w (F.reducedSquareCoefficientMap w
      (F.squareFiltration.quotientTop.polynomialSymbolMap w p))) α =
      F.reducedSquareGradedDifference e ω hF
        (coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w
            (F.squareFiltration.quotientTop.polynomialSymbolMap w p)) α) := by
  have hl : coefficients (F.firstCoefficientGradedPolynomial e ω hF w (F.reducedSquareCoefficientMap w
      (F.squareFiltration.quotientTop.polynomialSymbolMap w p))) α =
      F.gradedPieceProjection e ω hF (Finsupp.weight w α + 1)
        (F.reducedSquareDifference (coefficients p.val α)) := by
    rw [F.reducedSquareCoefficientMap_symbol, F.firstCoefficientGradedPolynomial_normalized,
      F.shiftedGradedPolynomial_coefficient, F.reducedSquareDifferenceRelative_coefficient]
  have hr : coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
      (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w
        (F.squareFiltration.quotientTop.polynomialSymbolMap w p)) α =
      F.squareFiltration.quotientTop.gradedPieceProjection
        (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
        (Finsupp.weight w α) (coefficients p.val α) := by
    rw [← F.squareFiltration.quotientTop.shiftedGradedPolynomial_zero
      (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w p,
      F.squareFiltration.quotientTop.shiftedGradedPolynomial_coefficient]
    simp only [Nat.add_zero]
  calc
    _ = F.gradedPieceProjection e ω hF (Finsupp.weight w α + 1)
        (F.reducedSquareDifference (coefficients p.val α)) := hl
    _ = F.reducedSquareGradedDifference e ω hF
        (F.squareFiltration.quotientTop.gradedPieceProjection
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
          (Finsupp.weight w α) (coefficients p.val α)) :=
      (F.reducedSquareGradedDifference_projection e ω hF (Finsupp.weight w α) (coefficients p.val α)).symm
    _ = _ := congrArg (F.reducedSquareGradedDifference e ω hF) hr.symm

theorem firstCoefficientGradedPolynomial_reducedSquare_coefficient
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (F.firstCoefficientGradedPolynomial e ω hF w (F.reducedSquareCoefficientMap w x)) α =
      F.reducedSquareGradedDifference e ω hF
        (coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w x) α) := by
  obtain ⟨p, rfl⟩ := F.squareFiltration.quotientTop.polynomialSymbolMap_surjective w x
  exact F.firstCoefficientGradedPolynomial_reducedSquare_symbol e ω hF w p α

theorem firstCoefficientGradedPolynomial_reducedSquare
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w) :
    F.firstCoefficientGradedPolynomial e ω hF w (F.reducedSquareCoefficientMap w x) =
      VectorPolynomial.map (F.reducedSquareGradedDifference e ω hF)
        (F.squareFiltration.quotientTop.gradedSymbolPolynomial
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w x) := by
  apply coefficients.injective
  ext α
  rw [coefficients_map, F.firstCoefficientGradedPolynomial_reducedSquare_coefficient]

theorem firstCoefficientGradedPolynomial_reducedSquare_homogeneous (α : σ →₀ ℕ)
    (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    F.firstCoefficientGradedPolynomial e ω hF w
        (F.reducedSquareCoefficientMap w
          (F.squareFiltration.quotientTop.homogeneousSymbolLift
            (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w α x)) =
      monomial α (basisGradeProjection (F.associatedGradedBasis e ω hF) ω (Finsupp.weight w α + 1)
        (F.reducedSquareGradedDifference e ω hF x)) := by
  rw [F.firstCoefficientGradedPolynomial_reducedSquare,
    F.squareFiltration.quotientTop.gradedSymbolPolynomial_homogeneousSymbolLift,
    VectorPolynomial.map_monomial, F.reducedSquareGradedDifference_gradeProjection]

theorem reducedSquareGradedSnd_coefficient
    (x : F.squareFiltration.quotientTop.PolynomialSymbol w) (α : σ →₀ ℕ) :
    F.reducedSquareGradedSndMap
        (coefficients (F.squareFiltration.quotientTop.gradedSymbolPolynomial
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w x) α) =
      coefficients (F.quotientTop.gradedSymbolPolynomial (F.quotientTopBasis e ω hF)
        (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w (F.reducedSquareSndSymbolMap w x)) α := by
  unfold reducedSquareGradedSndMap reducedSquareSndSymbolMap
  rw [F.squareFiltration.quotientTop.gradedSymbolPolynomial_filteredMap_coefficient
    F.quotientTop (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w x α]

theorem reducedSquareSnd_homogeneousSymbolLift (α : σ →₀ ℕ)
    (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    F.reducedSquareSndSymbolMap w
        (F.squareFiltration.quotientTop.homogeneousSymbolLift
          (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF) w α x) =
      F.quotientTop.homogeneousSymbolLift (F.quotientTopBasis e ω hF)
        (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w α (F.reducedSquareGradedSndMap x) := by
  exact F.squareFiltration.quotientTop.homogeneousSymbolLift_filteredMap
    F.quotientTop (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w α x

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

section General

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem gradedSymbolPolynomial_unit_eval (x : F.AssociatedGraded) :
    eval (fun _ : Unit => (1 : ℚ)) (F.gradedSymbolPolynomial e ω hF (fun _ : Unit => 1) x) = x := by
  have he : (eval (fun _ : Unit => (1 : ℚ))).comp
      (F.gradedSymbolPolynomial e ω hF (fun _ : Unit => 1)) = LinearMap.id := by
    apply (F.associatedGradedBasis e ω hF).ext
    intro i
    rw [LinearMap.comp_apply, F.associatedGradedBasis_apply, F.gradedSymbolPolynomial_basis,
      eval_monomial]
    simp
  exact LinearMap.congr_fun he x

theorem adaptedGradedPolynomialLie_unit_eval (p : F.adaptedLieSubalgebra (fun _ : Unit => 1)) :
    eval (fun _ : Unit => (1 : ℚ)) (F.adaptedGradedPolynomialLie e ω hF (fun _ : Unit => 1) p) =
      F.polynomialSymbolMap (fun _ : Unit => 1) p := by
  rw [F.adaptedGradedPolynomialLie_apply, F.adaptedShiftedGradedPolynomial_apply,
    F.shiftedGradedPolynomial_zero, F.gradedSymbolPolynomial_unit_eval]

end General

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem firstCoefficientGradedPolynomial_normalized_lie (w : σ → ℕ)
    (a : F.adaptedLieSubalgebra w) (p : F.normalizedRelativeSubmodule w) :
    F.firstCoefficientGradedPolynomial e ω hF w
      (F.normalizedFirstCoefficientMap w
        ⟨⁅a, p.val⁆, F.normalizedRelativeSubmodule_lie_mem w a p.val p.property⟩) =
      ⁅F.adaptedGradedPolynomialLie e ω hF w a,
        F.firstCoefficientGradedPolynomial e ω hF w (F.normalizedFirstCoefficientMap w p)⁆ := by
  rw [F.firstCoefficientGradedPolynomial_normalized, F.firstCoefficientGradedPolynomial_normalized]
  have he := F.adaptedShiftedGradedPolynomial_lie e ω hF w a p.val p.property.1
  simp only [F.adaptedShiftedGradedPolynomial_apply] at he
  rw [he]

theorem reducedSquareGradedDifference_unit (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    eval (fun _ : Unit => (1 : ℚ))
      (F.firstCoefficientGradedPolynomial e ω hF (fun _ : Unit => 1)
        (F.reducedSquareCoefficientMap (fun _ : Unit => 1) x)) =
      F.reducedSquareGradedDifference e ω hF x := by
  rw [F.firstCoefficientGradedPolynomial_reducedSquare, eval_map,
    F.squareFiltration.quotientTop.gradedSymbolPolynomial_unit_eval]

theorem reducedSquareGradedDifference_relative_lie
    (a : F.adaptedLieSubalgebra (fun _ : Unit => 1))
    (p : F.normalizedRelativeSubmodule (fun _ : Unit => 1)) :
    F.reducedSquareGradedDifference e ω hF
      ⁅F.reducedSquareDiagonalSymbolMap (fun _ : Unit => 1)
          (F.adaptedReducedSymbolMap (fun _ : Unit => 1) a),
        F.reducedRelativeSquareSymbolMap (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) p⁆ =
      ⁅F.polynomialSymbolMap (fun _ : Unit => 1) a,
        F.reducedSquareGradedDifference e ω hF
          (F.reducedRelativeSquareSymbolMap (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) p)⁆ := by
  rw [← F.reducedRelativeSquareSymbolMap_lie,
    ← F.reducedSquareGradedDifference_unit, F.reducedSquareCoefficientMap_relative,
    F.firstCoefficientGradedPolynomial_normalized_lie]
  change (evalLie (fun _ : Unit => (1 : ℚ))) ⁅_, _⁆ = _
  rw [LieHom.map_lie]
  simp only [evalLie_apply]
  rw [F.adaptedGradedPolynomialLie_unit_eval,
    ← F.reducedSquareCoefficientMap_relative (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) p,
    F.reducedSquareGradedDifference_unit]

end Erdos3.NilpotentLieFiltration

end

end OAI
