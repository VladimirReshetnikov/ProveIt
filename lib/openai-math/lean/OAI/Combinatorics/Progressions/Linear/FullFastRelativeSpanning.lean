import OAI.Combinatorics.Progressions.Dynamics.FastCoefficientGeneratorBudget
import OAI.Combinatorics.Progressions.Estimates.FastGradedRelativeInvariance
import OAI.Combinatorics.Progressions.Geometry.GradedTopCoordinates

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "ωQ" => (fun a : QuotientTopBasisIndex s ω => ω (Subtype.val a))
local notation "bQ" => F.quotientTop.associatedGradedBasis
  (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)

theorem reducedSquareGradedSndMap_basis_height (a : ReducedSquareBasisIndex s ω)
    (i : QuotientTopBasisIndex s ω) :
    RationalHeightLE ((bQ).repr (F.reducedSquareGradedSndMap (bW a)) i) 1 := by
  rw [F.reducedSquareGradedSndMap_coordinate e ω hF]
  exact basis_repr_height_one bW a _

variable [Fintype ι] [Fintype κ]

theorem exists_bounded_fast_graded_relative_kernel_generators
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∃ r : ℕ, r ≤ Fintype.card (QuotientTopBasisIndex s ω) ∧
      ∃ z : κ → F.squareFiltration.quotientTop.AssociatedGraded,
        Submodule.span ℚ (Set.range z) = F.fastGradedRelativeKernel W ∧
        ∀ j i, RationalHeightLE ((bW).repr (z j) i)
          (fastKernelGeneratorHeight (Fintype.card (ReducedSquareBasisIndex s ω))
            (Fintype.card κ) r H) := by
  have hPv (j : κ) (i : QuotientTopBasisIndex s ω) :
      RationalHeightLE ((bQ).repr (F.reducedSquareGradedSndMap (v j)) i)
        ((Fintype.card (ReducedSquareBasisIndex s ω) + 1) *
          H ^ Fintype.card (ReducedSquareBasisIndex s ω)) := by
    simpa only [mul_one, LieHom.coe_toLinearMap] using linearMap_coordinate_height
      bW bQ F.reducedSquareGradedSndMap.toLinearMap
      (F.reducedSquareGradedSndMap_basis_height e ω hF) (v j) (hv j) i
  have hB : 1 ≤ (Fintype.card (ReducedSquareBasisIndex s ω) + 1) *
      H ^ Fintype.card (ReducedSquareBasisIndex s ω) := by
    have hHp : 0 < H := hH
    exact Nat.succ_le_of_lt (by positivity)
  have he := exists_bounded_span_kernel_generators bW bQ
    F.reducedSquareGradedSndMap.toLinearMap v hB hv hPv
  simpa only [hspan, fastKernelGeneratorHeight, fastGradedRelativeKernel,
    LieHom.ker_toSubmodule] using he

theorem exists_bounded_full_fast_relative_generators
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H) :
    ∃ r : ℕ, r ≤ Fintype.card (QuotientTopBasisIndex s ω) ∧
      ∃ z : κ → F.AssociatedGraded,
        Submodule.span ℚ (Set.range z) = F.fullFastGradedRelative e ω hF W ∧
        ∀ j i, RationalHeightLE ((F.associatedGradedBasis e ω hF).repr (z j) i)
          (fastCoefficientGeneratorHeight (Fintype.card (ReducedSquareBasisIndex s ω))
            (Fintype.card κ) r H) := by
  obtain ⟨r, hr, z, hz, hzh⟩ :=
    F.exists_bounded_fast_graded_relative_kernel_generators e ω hF W v hspan hH hv
  refine ⟨r, hr, (F.reducedSquareGradedDifference e ω hF) ∘ z, ?_, fun j i => ?_⟩
  · rw [fullFastGradedRelative, ← hz, Submodule.map_span, ← Set.range_comp]
  · simpa only [Function.comp_apply, mul_one, fastCoefficientGeneratorHeight] using
      linearMap_coordinate_height bW (F.associatedGradedBasis e ω hF)
        (F.reducedSquareGradedDifference e ω hF)
        (F.reducedSquareGradedDifference_basis_height e ω hF) (z j) (hzh j) i

theorem exists_full_fast_relative_generators_exp
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ p)
    (hm : (Fintype.card κ : ℝ) ≤ p)
    (hq : (Fintype.card (QuotientTopBasisIndex s ω) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 40) ∧
      ∃ z : κ → F.AssociatedGraded,
        Submodule.span ℚ (Set.range z) = F.fullFastGradedRelative e ω hF W ∧
        ∀ j i, RationalHeightLE ((F.associatedGradedBasis e ω hF).repr (z j) i) H' := by
  obtain ⟨r, hr, z, hz, hzh⟩ :=
    F.exists_bounded_full_fast_relative_generators e ω hF W v hspan hH hv
  exact ⟨_, fastCoefficientGeneratorHeight_pos _ _ _ _ hH,
    fastCoefficientGeneratorHeight_le_exp _ _ _ _ hp hn hm
      ((Nat.cast_le.mpr hr).trans hq) hHp, z, hz, hzh⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
