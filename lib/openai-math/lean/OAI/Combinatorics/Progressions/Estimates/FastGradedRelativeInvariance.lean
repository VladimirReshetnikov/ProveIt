import OAI.Combinatorics.Progressions.Linear.RealGradedFastCoefficientKernel

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem reducedSquareGradedDifference_basis_height (a : ReducedSquareBasisIndex s ω) (i : ι) :
    RationalHeightLE ((F.associatedGradedBasis e ω hF).repr
      (F.reducedSquareGradedDifference e ω hF (bW a)) i) 1 := by
  rw [F.reducedSquareGradedDifference_basis]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl j =>
    simp only [Sum.elim_inl, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl
  | inr j => exact basis_repr_height_one (F.associatedGradedBasis e ω hF) j.val i

theorem reducedSquareGradedDifference_mem_second (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    F.reducedSquareGradedDifference e ω hF x ∈ F.associatedGradedFiltration.layer 2 := by
  have htop : (⊤ : Submodule ℚ F.squareFiltration.quotientTop.AssociatedGraded) ≤
      (F.associatedGradedFiltration.layer 2).comap (F.reducedSquareGradedDifference e ω hF) := by
    rw [← (bW).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change F.reducedSquareGradedDifference e ω hF (bW a) ∈ F.associatedGradedFiltration.layer 2
    rw [F.reducedSquareGradedDifference_basis]
    rcases a with ⟨a, ha⟩
    cases a with
    | inl i => exact (F.associatedGradedFiltration.layer 2).zero_mem
    | inr i =>
      rw [F.associatedGradedFiltration_layer e ω hF]
      exact Submodule.subset_span ⟨i.val, i.property, rfl⟩
  exact htop (by trivial)

variable (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem fastGradedRelativeKernel_graded
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    BasisGradedSubmodule bW ωW (F.fastGradedRelativeKernel W) := by
  intro j x hx
  refine ⟨hW j x hx.1, ?_⟩
  change F.reducedSquareGradedSndMap (basisGradeProjection bW ωW j x) = 0
  unfold reducedSquareGradedSndMap
  rw [F.squareFiltration.quotientTop.associatedGradedMap_gradeProjection F.quotientTop
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem j x]
  change basisGradeProjection (F.quotientTop.associatedGradedBasis (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF)) (fun i => ω i.val) j
      (F.reducedSquareGradedSndMap x) = 0
  rw [show F.reducedSquareGradedSndMap x = 0 from hx.2, map_zero]

theorem fullFastGradedRelative_le_second :
    F.fullFastGradedRelative e ω hF W ≤ F.associatedGradedFiltration.layer 2 := by
  rintro _ ⟨x, _, rfl⟩
  exact F.reducedSquareGradedDifference_mem_second e ω hF x

theorem fullFastGradedRelative_low_projection (j : ℕ) (hj : j < 2)
    (x : F.AssociatedGraded) (hx : x ∈ F.fullFastGradedRelative e ω hF W) :
    basisGradeProjection (F.associatedGradedBasis e ω hF) ω j x = 0 := by
  have hh := F.fullFastGradedRelative_le_second e ω hF W hx
  rw [F.associatedGradedFiltration_layer e ω hF] at hh
  apply (basisCoordinateProjection_eq_zero_iff (F.associatedGradedBasis e ω hF) {i | ω i = j} x).mpr
  apply Submodule.span_mono (Set.image_mono ?_) hh
  intro i hi
  change ω i ≠ j
  change 2 ≤ ω i at hi
  omega

theorem fullFastGradedRelative_graded
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω (F.fullFastGradedRelative e ω hF W) := by
  intro j x hx
  by_cases hj : j = 0
  · subst j
    rw [F.fullFastGradedRelative_low_projection e ω hF W 0 (by decide) x hx]
    exact (F.fullFastGradedRelative e ω hF W).zero_mem
  · obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨basisGradeProjection bW ωW (j - 1) y,
      F.fastGradedRelativeKernel_graded e ω hF W hW (j - 1) y hy, ?_⟩
    have he := F.reducedSquareGradedDifference_gradeProjection e ω hF (j - 1) y
    have hdeg : j - 1 + 1 = j := by omega
    simpa only [hdeg] using he

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem fullFastGradedRelative_lie_mem {u v : F.AssociatedGraded}
    (hu : u ∈ F.fullFastGradedDiagonal W) (hv : v ∈ F.fullFastGradedRelative e ω hF W) :
    ⁅u, v⁆ ∈ F.fullFastGradedRelative e ω hF W := by
  obtain ⟨z, hz, rfl⟩ := hv
  have hz0 : z ∈ (F.reducedSquareSndSymbolMap (fun _ : Unit => 1)).ker.toSubmodule := hz.2
  obtain ⟨p, hp⟩ := (F.reducedRelativeSquareSymbolMap_range
    (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one)).ge hz0
  obtain ⟨a, ha⟩ := F.polynomialSymbolMap_surjective (fun _ : Unit => 1) u
  have hua : F.adaptedReducedSymbolMap (fun _ : Unit => 1) a ∈
      F.reducedSquareFastDiagonalSubalgebra (fun _ : Unit => 1) W := by
    change F.quotientTopSymbolMap (fun _ : Unit => 1)
      (F.polynomialSymbolMap (fun _ : Unit => 1) a) ∈ _
    rw [ha]
    exact hu
  have hz' : z ∈ F.reducedSquareFastRelativeSubmodule (fun _ : Unit => 1) W := hz
  have hbr := F.reducedSquareFastRelative_action_mem (fun _ : Unit => 1) W
    (fun _ => Nat.zero_lt_one) hua hz'
  refine ⟨⁅F.reducedSquareDiagonalSymbolMap (fun _ : Unit => 1)
    (F.adaptedReducedSymbolMap (fun _ : Unit => 1) a), z⁆, hbr, ?_⟩
  rw [← hp, F.reducedSquareGradedDifference_relative_lie, ha]

theorem realFullFastGradedRelative_lie_mem {u v : ℝ ⊗[ℚ] F.AssociatedGraded}
    (hu : u ∈ realificationLieSubalgebra (F.fullFastGradedDiagonal W))
    (hv : v ∈ (F.fullFastGradedRelative e ω hF W).baseChange ℝ) :
    ⁅u, v⁆ ∈ (F.fullFastGradedRelative e ω hF W).baseChange ℝ :=
  lie_mem_real_baseChange (F.fullFastGradedDiagonal W).toSubmodule
    (F.fullFastGradedRelative e ω hF W) (F.fullFastGradedRelative e ω hF W)
    (fun _ hu _ hv => F.fullFastGradedRelative_lie_mem e ω hF W hu hv) hu hv

end Erdos3.NilpotentLieFiltration

end

end OAI
