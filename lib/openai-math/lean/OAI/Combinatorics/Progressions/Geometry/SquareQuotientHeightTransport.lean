import OAI.Combinatorics.Progressions.Estimates.CommonNativeSquareFactors
import OAI.Combinatorics.Progressions.Estimates.ReindexSymbolFactorization
import OAI.Combinatorics.Progressions.Linear.BasisFamilyLogHeight
import OAI.Combinatorics.Progressions.Linear.ReindexQuotientBasis

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (Γ : Subgroup F.squareFiltration.Group) (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ)
  (hout : bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ ⊆ denominatorGrid N)

local notation "Q" => F.squareFiltration.topQuotientModel (F.squareFinBasis b ω (hF 2))
  (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout
local notation "hQ" => F.squareFiltration.topQuotientModel_basis_layers
  (F.squareFinBasis b ω (hF 2)) (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout
local notation "bq" => F.reducedSquareBasis b ω hF
local notation "ωq" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "hq" => F.reducedSquareBasis_layers b ω hF

theorem squareTopQuotientModel_factorization_iff (T : σ → ℝ)
    (X : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (p : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    (Q).filtration.SymbolFactorizationIn (Q).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ T X p l W ↔
      F.squareFiltration.quotientTop.SymbolFactorizationIn bq ωq hq T X p l W := by
  exact F.squareFiltration.quotientTop.symbolFactorizationIn_iff_of_basis_reindex bq ωq hq
    (reducedSquareFinIndexEquiv s ω) (Q).basis
    (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ
    (F.squareTopQuotientModel_basis_reindex b ω hF Γ N hN hin hout) rfl T X p l W

theorem squareTopQuotientModel_graded_iff
    (U : Submodule ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    BasisGradedSubmodule ((Q).filtration.associatedGradedBasis (Q).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ)
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) U ↔
      BasisGradedSubmodule (F.squareFiltration.quotientTop.associatedGradedBasis bq ωq hq) ωq U := by
  exact F.squareFiltration.quotientTop.graded_submodule_iff_of_basis_reindex bq ωq hq
    (reducedSquareFinIndexEquiv s ω) (Q).basis
    (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ
    (F.squareTopQuotientModel_basis_reindex b ω hF Γ N hN hin hout) rfl U

theorem squareTopQuotientModel_graded_repr (x : F.squareFiltration.quotientTop.AssociatedGraded)
    (i : ReducedSquareBasisIndex s ω) :
    ((Q).filtration.associatedGradedBasis (Q).basis
      (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ).repr x
        (reducedSquareFinIndexEquiv s ω i) =
      (F.squareFiltration.quotientTop.associatedGradedBasis bq ωq hq).repr x i := by
  exact F.squareFiltration.quotientTop.associatedGradedBasis_repr_of_basis_reindex bq ωq hq
    (reducedSquareFinIndexEquiv s ω) (Q).basis
    (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ
    (F.squareTopQuotientModel_basis_reindex b ω hF Γ N hN hin hout) rfl x i

theorem squareTopQuotientModel_top_annihilation_iff
    (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    (∀ x ∈ W, basisGradeProjection ((Q).filtration.associatedGradedBasis (Q).basis
          (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ)
          (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) s x = x →
      (Q).filtration.gradedFrequency (Q).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ ξ x = 0) ↔
    (∀ x ∈ W, basisGradeProjection (F.squareFiltration.quotientTop.associatedGradedBasis bq ωq hq)
        ωq s x = x → F.squareFiltration.quotientTop.gradedFrequency bq ωq hq ξ x = 0) := by
  exact F.squareFiltration.quotientTop.graded_top_annihilation_iff_of_basis_reindex bq ωq hq
    (reducedSquareFinIndexEquiv s ω) (Q).basis
    (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ
    (F.squareTopQuotientModel_basis_reindex b ω hF Γ N hN hin hout) rfl ξ W

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem squareTopQuotientModel_graded_logHeight
    {ι κ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (Γ : Subgroup F.squareFiltration.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ)
    (hout : bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ ⊆ denominatorGrid N)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded) {p : ℝ}
    (hheight : BasisFamilyLogHeight
      ((F.squareFiltration.topQuotientModel (F.squareFinBasis b ω (hF 2))
        (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout).filtration.associatedGradedBasis
        (F.squareFiltration.topQuotientModel (F.squareFinBasis b ω (hF 2))
          (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i})
        (F.squareFiltration.topQuotientModel_basis_layers (F.squareFinBasis b ω (hF 2))
          (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout)) v p) :
    BasisFamilyLogHeight
      (F.squareFiltration.quotientTop.associatedGradedBasis
        (F.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (F.reducedSquareBasis_layers b ω hF)) v p := by
  intro i j
  have heq := F.squareTopQuotientModel_graded_repr b ω hF Γ N hN hin hout (v i) j
  exact (congrArg rationalLogHeight heq).symm.le.trans
    (hheight i (reducedSquareFinIndexEquiv s ω j))

end Erdos3.NilpotentLieFiltration

end

end OAI
