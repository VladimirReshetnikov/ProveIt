/- Modified for ProveIt: rewrite supported-basis coordinates with
semireducible transparency to align rational scalar instances on Lean 4.32.
The theorem statements are unchanged. -/
import OAI.Combinatorics.Progressions.Linear.SquareBasisGeometry

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : F.layer 2 = Submodule.span ℚ (e '' {i | 2 ≤ ω i}))

theorem adaptedSquareBasis_bracket_repr_inl (x y : F.squareLieSubalgebra) (k : ι) :
    (F.adaptedSquareBasis e ω hF).repr ⁅x, y⁆ (Sum.inl k) = e.repr ⁅x.val.2, y.val.2⁆ k := by
  change (F.squareBasis e _).repr ⁅x, y⁆ (Sum.inl k) = _
  rw [F.squareBasis_repr_inl]
  rfl

theorem adaptedSquareBasis_bracket_repr_inr (x y : F.squareLieSubalgebra) (k : {i // 2 ≤ ω i}) :
    (F.adaptedSquareBasis e ω hF).repr ⁅x, y⁆ (Sum.inr k) =
      e.repr (⁅x.val.1, y.val.1⁆ - ⁅x.val.2, y.val.2⁆) k.val := by
  change (F.squareBasis e _).repr ⁅x, y⁆ (Sum.inr k) = _
  rw [F.squareBasis_repr_inr]
  erw [supportedSubmoduleBasis_repr]
  rfl

theorem adaptedSquareBasis_structure_height {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (a b k : ι ⊕ {i // 2 ≤ ω i}) :
    RationalHeightLE ((F.adaptedSquareBasis e ω hF).repr
      ⁅F.adaptedSquareBasis e ω hF a, F.adaptedSquareBasis e ω hF b⁆ k) H := by
  rcases a with i | i <;> rcases b with j | j <;> rcases k with k | k
  · rw [F.adaptedSquareBasis_bracket_repr_inl, F.adaptedSquareBasis_inl, F.adaptedSquareBasis_inl]
    exact hc i j k
  · rw [F.adaptedSquareBasis_bracket_repr_inr, F.adaptedSquareBasis_inl, F.adaptedSquareBasis_inl]
    simpa only [sub_self, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  · rw [F.adaptedSquareBasis_bracket_repr_inl, F.adaptedSquareBasis_inl, F.adaptedSquareBasis_inr]
    simpa only [lie_zero, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  · rw [F.adaptedSquareBasis_bracket_repr_inr, F.adaptedSquareBasis_inl, F.adaptedSquareBasis_inr]
    simpa only [lie_zero, sub_zero] using hc i j.val k.val
  · rw [F.adaptedSquareBasis_bracket_repr_inl, F.adaptedSquareBasis_inr, F.adaptedSquareBasis_inl]
    simpa only [zero_lie, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  · rw [F.adaptedSquareBasis_bracket_repr_inr, F.adaptedSquareBasis_inr, F.adaptedSquareBasis_inl]
    simpa only [zero_lie, sub_zero] using hc i.val j k.val
  · rw [F.adaptedSquareBasis_bracket_repr_inl, F.adaptedSquareBasis_inr, F.adaptedSquareBasis_inr]
    simpa only [lie_zero, map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  · rw [F.adaptedSquareBasis_bracket_repr_inr, F.adaptedSquareBasis_inr, F.adaptedSquareBasis_inr]
    simpa only [lie_zero, sub_zero] using hc i.val j.val k.val

variable (F : NilpotentLieFiltration L (s + 1))

theorem reducedSquareBasis_structure_height
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    {H : ℕ} (hH : 1 ≤ H) (hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (a b k : ReducedSquareBasisIndex s ω) :
    RationalHeightLE ((F.reducedSquareBasis e ω hF).repr
      ⁅F.reducedSquareBasis e ω hF a, F.reducedSquareBasis e ω hF b⁆ k) H := by
  change RationalHeightLE (lieStructureConstants (F.reducedSquareBasis e ω hF) a b k) H
  have hspan : (F.squareFiltration.layerIdeal (s + 1)).toSubmodule = Submodule.span ℚ
      (F.adaptedSquareBasis e ω (hF 2) '' {i | s + 1 ≤ squareBasisWeight ω i}) :=
    F.adaptedSquareBasis_layers e ω hF (s + 1)
  have he : lieStructureConstants (F.reducedSquareBasis e ω hF) a b k =
      lieStructureConstants (F.adaptedSquareBasis e ω (hF 2)) a.val b.val k.val :=
    supportedQuotientBasis_lieStructure (F.adaptedSquareBasis e ω (hF 2))
      (F.squareFiltration.layerIdeal (s + 1)) {i | s + 1 ≤ squareBasisWeight ω i} hspan a b k
  rw [he]
  exact F.adaptedSquareBasis_structure_height e ω (hF 2) hH hc a.val b.val k.val

end Erdos3.NilpotentLieFiltration

end

end OAI
