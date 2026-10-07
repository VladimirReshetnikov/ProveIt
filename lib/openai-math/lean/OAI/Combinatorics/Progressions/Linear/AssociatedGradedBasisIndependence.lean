/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Polynomial.RealCoordinatePolynomialSymbol

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def gradedPieceProjection (j : ℕ) : L →ₗ[ℚ] F.AssociatedGraded :=
  (F.associatedGradedBasis b ω hlayers).repr.symm.toLinearMap.comp
    (b.repr.toLinearMap.comp (basisGradeProjection b ω j))

theorem gradedPieceProjection_coordinate (j : ℕ) (v : L) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr (F.gradedPieceProjection b ω hlayers j v) i =
      if ω i = j then b.repr v i else 0 := by
  simp only [gradedPieceProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, basisGradeProjection_repr]

theorem gradedPieceProjection_eq_pieceMap (j : ℕ) (v : F.layer j) :
    F.gradedPieceProjection b ω hlayers j v = F.associatedGradedPieceMap j v := by
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  rw [F.gradedPieceProjection_coordinate, F.associatedGradedPieceMap_coordinate]
  simp only [eq_comm]

theorem gradedRefiltrationLayer_eq_inf_comap (U : LieSubalgebra ℚ F.AssociatedGraded) (j : ℕ) :
    F.gradedRefiltrationLayer U j =
      F.layer j ⊓ U.toSubmodule.comap (F.gradedPieceProjection b ω hlayers j) := by
  ext v
  rw [F.mem_gradedRefiltrationLayer, Submodule.mem_inf, Submodule.mem_comap]
  constructor
  · rintro ⟨hv, hU⟩
    exact ⟨hv, (F.gradedPieceProjection_eq_pieceMap b ω hlayers j ⟨v, hv⟩).symm ▸ hU⟩
  · rintro ⟨hv, hU⟩
    exact ⟨hv, F.gradedPieceProjection_eq_pieceMap b ω hlayers j ⟨v, hv⟩ ▸ hU⟩

theorem real_gradedPieceProjection_coordinate (j : ℕ) (v : ℝ ⊗[ℚ] L) (i : ι) :
    ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr
      ((F.gradedPieceProjection b ω hlayers j).baseChange ℝ v) i =
      if ω i = j then (b.baseChange ℝ).repr v i else 0 := by
  induction v using TensorProduct.inductionOn with
  | tmul a v =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      F.gradedPieceProjection_coordinate, Basis.baseChange_repr_tmul]
    split_ifs <;> simp only [zero_smul]
  | add v z hv hz =>
    simp only [map_add, Finsupp.add_apply, hv, hz]
    split_ifs <;> simp only [add_zero]

theorem realGradedSymbolPolynomial_coefficient_of_polynomial
    (w : σ → ℕ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (α : σ →₀ ℕ) :
    coefficients (F.realGradedSymbolPolynomial b ω hlayers w
      (F.realSymbolOfPolynomial b ω hlayers w p)) α =
        (F.gradedPieceProjection b ω hlayers (Finsupp.weight w α)).baseChange ℝ (coefficients p α) := by
  apply ((F.associatedGradedBasis b ω hlayers).baseChange ℝ).repr.injective
  ext i
  rw [F.real_gradedPieceProjection_coordinate]
  by_cases h : Finsupp.weight w α = ω i
  · rw [ite_eq_left h.symm]
    exact (F.realGradedSymbolPolynomial_coordinate b ω hlayers w _ ⟨(α, i), h⟩).trans
      (F.realSymbolOfPolynomial_coordinate b ω hlayers w p ⟨(α, i), h⟩)
  · rw [ite_eq_right (Ne.symm h)]
    exact F.realGradedSymbolPolynomial_coordinate_of_ne b ω hlayers w _ α i h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hb : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem associatedGradedPieceMap_repr_symm (j : ℕ) (x : F.layer j) :
    b.repr.symm ((F.associatedGradedBasis b ω hb).repr (F.associatedGradedPieceMap j x)) =
      basisGradeProjection b ω j x.val := by
  apply b.repr.injective
  ext i
  rw [b.repr.apply_symm_apply, F.associatedGradedPieceMap_coordinate,
    basisGradeProjection_repr]
  simp only [eq_comm]

theorem associatedGradedBasis_repr_symm_eq_projection
    (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hc : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})) (i : κ) :
    b.repr.symm ((F.associatedGradedBasis b ω hb).repr
      (F.associatedGradedBasis c ν hc i)) = basisGradeProjection b ω (ν i) (c i) := by
  rw [← F.associatedGradedPieceMap_basis c ν hc (ν i) i le_rfl rfl]
  exact F.associatedGradedPieceMap_repr_symm b ω hb (ν i) _

theorem associatedGradedBasis_repr_change
    (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hc : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})) (i : κ) (k : ι) :
    (F.associatedGradedBasis b ω hb).repr (F.associatedGradedBasis c ν hc i) k =
      if ω k = ν i then b.repr (c i) k else 0 := by
  have h := congrArg (fun x : L => b.repr x k)
    (F.associatedGradedBasis_repr_symm_eq_projection b ω hb c ν hc i)
  simpa only [b.repr.apply_symm_apply, basisGradeProjection_repr] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hb : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem associatedGradedBasis_projection_pieceMap (r j : ℕ) (x : F.layer j) :
    basisGradeProjection (F.associatedGradedBasis b ω hb) ω r (F.associatedGradedPieceMap j x) =
      if j = r then F.associatedGradedPieceMap j x else 0 := by
  classical
  apply (F.associatedGradedBasis b ω hb).repr.injective
  ext i
  rw [basisGradeProjection_repr, F.associatedGradedPieceMap_coordinate]
  split_ifs <;> simp_all only [F.associatedGradedPieceMap_coordinate,
    map_zero, Finsupp.zero_apply, ite_true, ite_false, eq_comm, not_true_eq_false]

theorem associatedGradedBasis_projection_independent
    (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hc : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})) (r : ℕ) :
    basisGradeProjection (F.associatedGradedBasis b ω hb) ω r =
      basisGradeProjection (F.associatedGradedBasis c ν hc) ν r := by
  apply (F.associatedGradedBasis b ω hb).ext
  intro i
  rw [← F.associatedGradedPieceMap_basis b ω hb (ω i) i le_rfl rfl,
    F.associatedGradedBasis_projection_pieceMap b ω hb,
    F.associatedGradedBasis_projection_pieceMap c ν hc]

theorem associatedGradedBasis_gradedSubmodule_independent
    (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hc : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (U : Submodule ℚ F.AssociatedGraded) :
    BasisGradedSubmodule (F.associatedGradedBasis b ω hb) ω U ↔
      BasisGradedSubmodule (F.associatedGradedBasis c ν hc) ν U := by
  unfold BasisGradedSubmodule
  simp only [F.associatedGradedBasis_projection_independent b ω hb c ν hc]

end Erdos3.NilpotentLieFiltration

end

end OAI
