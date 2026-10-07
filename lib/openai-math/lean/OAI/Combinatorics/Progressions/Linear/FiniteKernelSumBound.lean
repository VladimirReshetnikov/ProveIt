import OAI.Combinatorics.Progressions.Estimates.FiniteEqualityPatternCard

namespace OAI

section

namespace Erdos3

variable {S I : Type*}

def kernelFiberEmbeddingEquiv (r : Setoid S) :
    {a : S → I // Setoid.ker a = r} ≃ (Quotient r ↪ I) where
  toFun a := ⟨Quotient.lift a.1 a.2.symm.le,
    (Setoid.lift_injective_iff_ker_eq_of_le a.2.symm.le).mpr a.2⟩
  invFun b := ⟨fun i => b (Quotient.mk'' i), by
    apply Setoid.ext
    intro i j
    change b (Quotient.mk'' i) = b (Quotient.mk'' j) ↔ r i j
    rw [b.injective.eq_iff, Quotient.eq]⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv b := by
    apply Function.Embedding.ext
    intro i
    induction i using Quotient.inductionOn with
    | h i => rfl

theorem kernelFiberEmbeddingEquiv_apply (r : Setoid S)
    (a : {a : S → I // Setoid.ker a = r}) (i : S) :
    kernelFiberEmbeddingEquiv r a (Quotient.mk'' i) = a.1 i := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
  [DecidableEq I] [DecidableEq (Setoid S)]

omit [DecidableEq I] in
theorem finiteKernelFiber_sum (r : Setoid S) [Fintype (Quotient r)]
    (G : (S → I) → ℝ) :
    (∑ a : {a : S → I // Setoid.ker a = r}, G a.1) =
      ∑ b : Quotient r ↪ I, G (fun i => b (Quotient.mk'' i)) := by
  exact Fintype.sum_equiv (kernelFiberEmbeddingEquiv r) _ _ (fun _ => rfl)

omit [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I] in
theorem finiteKernel_sum_grouped (T : Finset (S → I)) (G : (S → I) → ℝ) :
    (∑ a ∈ T, G a) = ∑ r ∈ T.image Setoid.ker, ∑ a ∈ T.filter (fun a => Setoid.ker a = r), G a := by
  exact (Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) G).symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
  [DecidableEq I] [DecidableEq (Setoid S)]

omit [DecidableEq I] in
theorem finiteKernel_filter_sum_le (T : Finset (S → I)) (G : (S → I) → ℝ)
    (hG : ∀ a, 0 ≤ G a) (r : Setoid S) :
    (∑ a ∈ T.filter (fun a => Setoid.ker a = r), G a) ≤
      ∑ a : {a : S → I // Setoid.ker a = r}, G a.1 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a : S → I => Setoid.ker a = r))
    (fun a => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]) G]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ (Finset.subset_univ T))
  intro a _ _
  exact hG a

omit [DecidableEq I] in
theorem finiteKernel_sum_bound (T : Finset (S → I)) (G : (S → I) → ℝ)
    (hG : ∀ a, 0 ≤ G a) (B : ℝ) (hB : 0 ≤ B)
    (hpattern : ∀ r ∈ T.image Setoid.ker,
      (∑ a : {a : S → I // Setoid.ker a = r}, G a.1) ≤ B) :
    (∑ a ∈ T, G a) ≤ (Fintype.card S ^ Fintype.card S : ℕ) * B := by
  rw [finiteKernel_sum_grouped]
  calc
    _ ≤ ∑ r ∈ T.image Setoid.ker, B := by
      apply Finset.sum_le_sum
      intro r hr
      exact (finiteKernel_filter_sum_le T G hG r).trans (hpattern r hr)
    _ = ((T.image Setoid.ker).card : ℝ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card S ^ Fintype.card S : ℕ) * B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast finiteEqualityPatterns_card_le_card (T.image Setoid.ker)) hB

end Erdos3

end

end OAI
