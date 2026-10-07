import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI

section

namespace Erdos3

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_nested_independent_spanning_sets (n : ℕ) :
    ∀ (P : Fin n → Submodule K V) (S : Set V), Antitone P →
      (∀ i, Submodule.span K (S ∩ (P i : Set V)) = P i) →
      ∃ B : Set V, B ⊆ S ∧ LinearIndepOn K id B ∧
        Submodule.span K B = Submodule.span K S ∧
        ∃ T : Fin n → Set V, Antitone T ∧ (∀ i, T i ⊆ B) ∧
          ∀ i, Submodule.span K (T i) = P i := by
  induction n with
  | zero =>
      intro P S _ _
      let h := linearIndepOn_empty K (id : V → V)
      let hsub : (∅ : Set V) ⊆ S := Set.empty_subset S
      refine ⟨h.extend hsub, h.extend_subset hsub, h.linearIndepOn_extend hsub,
        h.span_extend_eq_span hsub, Fin.elim0, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      intro P S hP hspan
      let S₀ := S ∩ (P 0 : Set V)
      let P' : Fin n → Submodule K V := fun i => P i.succ
      have hP' : Antitone P' := fun i j hij => hP (by simpa using hij)
      have hspan' (i : Fin n) : Submodule.span K (S₀ ∩ (P' i : Set V)) = P' i := by
        have heq : S₀ ∩ (P' i : Set V) = S ∩ (P i.succ : Set V) := by
          ext x
          constructor
          · exact fun hx => ⟨hx.1.1, hx.2⟩
          · exact fun hx => ⟨⟨hx.1, hP (Fin.zero_le i.succ) hx.2⟩, hx.2⟩
        rw [heq]
        exact hspan i.succ
      obtain ⟨B₀, hB₀, hiB₀, hspB₀, T₀, hT₀, hTB₀, hspT₀⟩ := ih P' S₀ hP' hspan'
      have hBS : B₀ ⊆ S := fun _ hx => (hB₀ hx).1
      let B := hiB₀.extend hBS
      have hB₀B : B₀ ⊆ B := hiB₀.subset_extend hBS
      let T : Fin (n + 1) → Set V := Fin.cases B₀ T₀
      refine ⟨B, hiB₀.extend_subset hBS, hiB₀.linearIndepOn_extend hBS,
        hiB₀.span_extend_eq_span hBS, T, ?_, ?_, ?_⟩
      · intro i j hij
        obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
        · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
          · exact Set.Subset.rfl
          · exact hTB₀ j
        · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
          · exact False.elim ((not_le_of_gt (Fin.succ_pos i)) hij)
          · exact hT₀ (by simpa using hij)
      · intro i
        exact Fin.cases hB₀B (fun j => (hTB₀ j).trans hB₀B) i
      · intro i
        refine Fin.cases ?_ (fun j => hspT₀ j) i
        exact hspB₀.trans (hspan 0)

end Erdos3

end

end OAI
