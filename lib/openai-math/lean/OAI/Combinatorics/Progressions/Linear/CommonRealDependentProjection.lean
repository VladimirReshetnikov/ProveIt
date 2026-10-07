import OAI.Combinatorics.Progressions.Estimates.BoundedNativeDependentApproximations

namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} [Fintype κ] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (d : Fin (s + 1)) (f : Basis κ ℚ (W.L ⧸ W.rank.filtration.layer d.val 2))

theorem coordinateSpace_first :
    fourFirstProjection (D.coordinateSpace d f) =
      (fourFirstProjection (D.horizontal d)).map (W.rank.filtration.higherHorizontalCoordinates d.val f) :=
  fourFirstProjection_map (W.rank.filtration.higherHorizontalCoordinates d.val f) (D.horizontal d)

theorem coordinateSpace_sparse (S : Finset (Fin 4)) :
    fourSparseFirstProjection (D.coordinateSpace d f) S =
      (fourSparseFirstProjection (D.horizontal d) S).map
        (W.rank.filtration.higherHorizontalCoordinates d.val f) :=
  fourSparseFirstProjection_map (W.rank.filtration.higherHorizontalCoordinates d.val f)
    (W.rank.filtration.higherHorizontalCoordinates_injective d.val f) (D.horizontal d) S

theorem coordinateSpace_dependent :
    fourDependentProjection (D.coordinateSpace d f) =
      (fourDependentProjection (D.horizontal d)).map
        (W.rank.filtration.higherHorizontalCoordinates d.val f) :=
  fourDependentProjection_map (W.rank.filtration.higherHorizontalCoordinates d.val f)
    (W.rank.filtration.higherHorizontalCoordinates_injective d.val f) (D.horizontal d)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeDegreeRankFamily

theorem nativeCoefficientCoordinates_eq_real
    {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (hs : 1 ≤ s)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (α : Unit →₀ ℕ)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    (h : ZMod N) :
    W.nativeCoefficientCoordinates hs c τ hG α f h =
      W.rank.filtration.realHigherHorizontalCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
        (W.horizontalCoefficient hs c τ hG α h) := by
  funext i
  exact (W.rank.filtration.realHigherHorizontalCoordinates_component
    (Finsupp.weight (fun _ : Unit => 1) α) f (W.horizontalCoefficient hs c τ hG α h) i).symm

end NativeDegreeRankFamily

namespace NativeRankRelation.CommonData

variable {ι κ : Type*} [Fintype ι] {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}

theorem real_dependent_coordinateSpace_eq (D : R.CommonData P) (d : Fin (s + 1))
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer d.val 2)) :
    realRationalCoordinateSpan (fourDependentProjection (D.coordinateSpace d f)) =
      ((fourDependentProjection (D.horizontal d)).baseChange ℝ).map
        (W.rank.filtration.realHigherHorizontalCoordinates d.val f) := by
  rw [D.coordinateSpace_dependent]
  exact (W.rank.filtration.realHigherHorizontalCoordinates_image d.val f
    (fourDependentProjection (D.horizontal d))).symm

theorem exists_real_dependent_remainder (D : R.CommonData P) (d : Fin (s + 1))
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer d.val 2))
    (x y : ℝ ⊗[ℚ] W.rank.filtration.HigherHorizontal d.val) (e u : ι → ℝ)
    (hmem : W.rank.filtration.realHigherHorizontalCoordinates d.val f x -
        W.rank.filtration.realHigherHorizontalCoordinates d.val f y - e - u ∈
      realRationalCoordinateSpan (fourDependentProjection (D.coordinateSpace d f))) :
    ∃ z ∈ (fourDependentProjection (D.horizontal d)).baseChange ℝ,
      W.rank.filtration.realHigherHorizontalCoordinates d.val f (x - y - z) = e + u := by
  rw [D.real_dependent_coordinateSpace_eq d f] at hmem
  obtain ⟨z, hz, hcoord⟩ := hmem
  refine ⟨z, hz, ?_⟩
  rw [map_sub, map_sub, hcoord]
  abel

theorem exists_native_dependent_remainder (D : R.CommonData P) (hs : 1 ≤ s)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (f : Basis ι ℚ (W.L ⧸ W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2))
    (h h₀ : ZMod N) (e u : ι → ℝ)
    (hmem : W.nativeCoefficientCoordinates hs c τ hG α f h -
        W.nativeCoefficientCoordinates hs c τ hG α f h₀ - e - u ∈
      realRationalCoordinateSpan (fourDependentProjection
        (D.coordinateSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f))) :
    ∃ z ∈ (fourDependentProjection
        (D.horizontal ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩)).baseChange ℝ,
      W.rank.filtration.realHigherHorizontalCoordinates (Finsupp.weight (fun _ : Unit => 1) α) f
        (W.horizontalCoefficient hs c τ hG α h - W.horizontalCoefficient hs c τ hG α h₀ - z) = e + u := by
  apply D.exists_real_dependent_remainder
    ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ f
    (W.horizontalCoefficient hs c τ hG α h) (W.horizontalCoefficient hs c τ hG α h₀) e u
  simpa only [W.nativeCoefficientCoordinates_eq_real hs c τ hG α f] using hmem

end NativeRankRelation.CommonData

end Erdos3

end

end OAI
