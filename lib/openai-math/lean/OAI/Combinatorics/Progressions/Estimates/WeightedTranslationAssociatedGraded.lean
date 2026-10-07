/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Nilpotent.CurrentBracketInductionStep

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def homogeneousAssociatedGradedEquiv
    (hb : BasisHomogeneousBrackets b ω) : F.AssociatedGraded ≃ₗ⁅ℚ⁆ L :=
  { (F.associatedGradedBasis b ω hF).repr.trans b.repr.symm with
    map_lie' {x y} := by
      let f := (F.associatedGradedBasis b ω hF).repr.trans b.repr.symm
      change f ⁅x, y⁆ = ⁅f x, f y⁆
      apply linear_map_lie_of_basis (F.associatedGradedBasis b ω hF) f.toLinearMap
      intro i j
      apply b.repr.injective
      ext k
      have hf (z : F.AssociatedGraded) : b.repr (f z) =
          (F.associatedGradedBasis b ω hF).repr z := b.repr.apply_symm_apply _
      have hbi (a : ι) : f (F.associatedGradedBasis b ω hF a) = b a := by
        apply b.repr.injective
        rw [hf]
        simp only [Basis.repr_self]
      change b.repr (f ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆) k =
        b.repr ⁅f (F.associatedGradedBasis b ω hF i), f (F.associatedGradedBasis b ω hF j)⁆ k
      rw [hf, hbi, hbi, F.associatedGradedBasis_bracket]
      by_cases h : ω i + ω j = ω k
      · simp only [h, ite_true]
      · rw [ite_eq_right h, hb i j k (Ne.symm h)] }

@[simp] theorem homogeneousAssociatedGradedEquiv_repr
    (hb : BasisHomogeneousBrackets b ω) (x : F.AssociatedGraded) (i : ι) :
    b.repr (F.homogeneousAssociatedGradedEquiv b ω hF hb x) i =
      (F.associatedGradedBasis b ω hF).repr x i := by
  exact congrArg (fun z : ι →₀ ℚ => z i) (b.repr.apply_symm_apply _)

@[simp] theorem homogeneousAssociatedGradedEquiv_basis
    (hb : BasisHomogeneousBrackets b ω) (i : ι) :
    F.homogeneousAssociatedGradedEquiv b ω hF hb (F.associatedGradedBasis b ω hF i) = b i := by
  apply b.repr.injective
  ext k
  rw [homogeneousAssociatedGradedEquiv_repr]
  simp only [Basis.repr_self]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.PolynomialTranslationLie
open Module
variable {σ : Type*} [Fintype σ]

noncomputable def weightedAssociatedGradedEquiv (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    (weightedFiltration w d hwd).AssociatedGraded ≃ₗ⁅ℚ⁆ weightedSubalgebra w d :=
  (weightedFiltration w d hwd).homogeneousAssociatedGradedEquiv
    (weightedBasis w d hw) (weightedBasisGrade w d)
    (weightedFiltration_layer_eq_span w d hw hwd)
    (weightedBasis_homogeneous_brackets w d hw)

@[simp] theorem weightedAssociatedGradedEquiv_repr (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : (weightedFiltration w d hwd).AssociatedGraded) (i : WeightedBasisIndex w d) :
    (weightedBasis w d hw).repr (weightedAssociatedGradedEquiv w d hw hwd x) i =
      ((weightedFiltration w d hwd).associatedGradedBasis (weightedBasis w d hw)
        (weightedBasisGrade w d) (weightedFiltration_layer_eq_span w d hw hwd)).repr x i :=
  (weightedFiltration w d hwd).homogeneousAssociatedGradedEquiv_repr _ _ _ _ x i

end Erdos3.PolynomialTranslationLie

end

end OAI
