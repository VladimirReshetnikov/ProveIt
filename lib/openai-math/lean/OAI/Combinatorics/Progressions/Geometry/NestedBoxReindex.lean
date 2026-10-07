import OAI.Combinatorics.Progressions.Estimates.NestedProgressionReindex
import OAI.Combinatorics.Progressions.Probability.ProductSliceAxisDensity

namespace OAI

section

namespace Erdos3

theorem exists_nested_box_affine {I : Type*} [Fintype I] [DecidableEq I]
    (c b : I → ℤ) {m d : ℕ} (hm : 0 < m) (hd : 0 < d)
    (H L : I → ℕ) (hL : ∀ i, 0 < L i)
    (hsub : commonStrideBox b d L ⊆ commonStrideBox c m H) :
    ∃ (A : I → I → ℤ) (a : I → ℤ), ∀ x ∈ integerBox L,
      integerAffineMap A a x ∈ integerBox H ∧
      commonStridePoint b d x = commonStridePoint c m (integerAffineMap A a x) := by
  have haxis (i : I) : (integerProgressionSupport (b i) d (L i)).Nonempty :=
    Finset.card_pos.mp (by simpa only [card_integerProgressionSupport _ _ _ hd] using hL i)
  have hcoord (i : I) := piFinset_axis_subset _ _ haxis hsub i
  choose a s ha using fun i => exists_nested_progression_affine (c i) (b i) hm hd (hL i) (hcoord i)
  refine ⟨(fun i j => if i = j then s i else 0), a, fun x hx => ?_⟩
  rw [integerAffineMap_diagonal]
  have hb (i : I) := ha i (x i) ((mem_integerBox L x).mp hx i).1 ((mem_integerBox L x).mp hx i).2
  refine ⟨(mem_integerBox H _).mpr (fun i => ⟨(hb i).1, (hb i).2.1⟩), ?_⟩
  funext i
  exact (hb i).2.2

end Erdos3

end

end OAI
