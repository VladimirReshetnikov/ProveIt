/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.ProjectedPointwiseCoefficient
import OAI.Combinatorics.Progressions.Estimates.WeightedTranslationAssociatedGraded

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module
variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

noncomputable def homogeneousGradedProjection : F.AssociatedGraded →ₗ⁅ℚ⁆ M :=
  (G.homogeneousAssociatedGradedEquiv c ν hG hc).toLieHom.comp
    (F.associatedGradedMap G φ hφ)

@[simp] theorem homogeneousGradedProjection_repr (x : F.AssociatedGraded) (j : κ) :
    c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ x) j =
      (G.associatedGradedBasis c ν hG).repr (F.associatedGradedMap G φ hφ x) j :=
  G.homogeneousAssociatedGradedEquiv_repr c ν hG hc _ j

variable (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousGradedProjection_basis_repr (i : ι) (j : κ) :
    c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ
      (F.associatedGradedBasis b ω hF i)) j =
      if ω i = ν j then c.repr (φ (b i)) j else 0 := by
  rw [F.homogeneousGradedProjection_repr,
    F.associatedGradedMap_basis_repr G b ω hF c ν hG φ hφ]

theorem homogeneousGradedProjection_gradeProjection (r : ℕ) (x : F.AssociatedGraded) :
    F.homogeneousGradedProjection G c ν hG hc φ hφ
      (basisGradeProjection (F.associatedGradedBasis b ω hF) ω r x) =
      basisGradeProjection c ν r (F.homogeneousGradedProjection G c ν hG hc φ hφ x) := by
  apply basisBlockMap_commutes (F.associatedGradedBasis b ω hF) c ω ν
    (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap
  intro i j hij
  change c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ
    (F.associatedGradedBasis b ω hF i)) j = 0
  rw [F.homogeneousGradedProjection_basis_repr G c ν hG hc φ hφ b ω hF]
  exact ite_eq_right (Ne.symm hij)

theorem homogeneousGradedProjection_image_graded
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule) :
    BasisGradedSubmodule c ν
      (W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ)).toSubmodule := by
  rintro r y ⟨x, hx, rfl⟩
  exact ⟨basisGradeProjection (F.associatedGradedBasis b ω hF) ω r x, hW r x hx,
    F.homogeneousGradedProjection_gradeProjection G c ν hG hc φ hφ b ω hF r x⟩

 theorem homogeneousGradedProjection_span {J : Type*}
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : J → F.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule) :
    Submodule.span ℚ (Set.range (fun j => F.homogeneousGradedProjection G c ν hG hc φ hφ (v j))) =
      (W.map (F.homogeneousGradedProjection G c ν hG hc φ hφ)).toSubmodule := by
  change _ = W.toSubmodule.map (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap
  rw [← hv, Submodule.map_span]
  congr 1
  exact Set.range_comp _ _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped BigOperators

variable {ι κ L M : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hc : BasisHomogeneousBrackets c ν)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem homogeneousGradedProjection_repr_sum (x : F.AssociatedGraded) (j : κ) :
    c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ x) j =
      ∑ i, (F.associatedGradedBasis b ω hF).repr x i *
        (if ω i = ν j then c.repr (φ (b i)) j else 0) := by
  classical
  conv_lhs => rw [← (F.associatedGradedBasis b ω hF).sum_repr x]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, F.homogeneousGradedProjection_basis_repr G c ν hG hc φ hφ b ω hF]

theorem homogeneousGradedProjection_coordinate_height {H K : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b i)) j) H)
    (x : F.AssociatedGraded)
    (hx : ∀ i, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr x i) K) (j : κ) :
    RationalHeightLE (c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ x) j)
      ((Fintype.card ι + 1) * (K * H) ^ Fintype.card ι) := by
  apply linearMap_coordinate_height (F.associatedGradedBasis b ω hF) c
    (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap _ x hx j
  intro i k
  change RationalHeightLE (c.repr
    (F.homogeneousGradedProjection G c ν hG hc φ hφ (F.associatedGradedBasis b ω hF i)) k) H
  rw [F.homogeneousGradedProjection_basis_repr G c ν hG hc φ hφ b ω hF]
  split_ifs
  · exact hentries i k
  · exact ⟨by simp, by simpa using hH⟩

theorem homogeneousGradedProjection_coordinate_logHeight {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ p)
    (x : F.AssociatedGraded)
    (hx : ∀ i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr x i) ≤ p) (j : κ) :
    rationalLogHeight (c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ x) j) ≤
      (p + 2) ^ 4 := by
  apply rational_functional_value_logHeight (F.associatedGradedBasis b ω hF)
    ((c.coord j).comp (F.homogeneousGradedProjection G c ν hG hc φ hφ).toLinearMap)
    hp hι _ x hx
  intro i
  change rationalLogHeight (c.repr
    (F.homogeneousGradedProjection G c ν hG hc φ hφ (F.associatedGradedBasis b ω hF i)) j) ≤ p
  rw [F.homogeneousGradedProjection_basis_repr G c ν hG hc φ hφ b ω hF]
  split_ifs
  · exact hentries i j
  · simpa [rationalLogHeight] using hp

theorem homogeneousGradedProjection_coordinate_ceil_height {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hentries : ∀ i j, rationalLogHeight (c.repr (φ (b i)) j) ≤ p)
    (x : F.AssociatedGraded)
    (hx : ∀ i, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr x i) ≤ p) (j : κ) :
    RationalHeightLE (c.repr (F.homogeneousGradedProjection G c ν hG hc φ hφ x) j)
      ⌈Real.exp ((p + 2) ^ 4)⌉₊ :=
  rationalHeightLE_ceil_exp
    (F.homogeneousGradedProjection_coordinate_logHeight G c ν hG hc φ hφ b ω hF
      hp hι hentries x hx j)

end Erdos3.NilpotentLieFiltration

end

end OAI
