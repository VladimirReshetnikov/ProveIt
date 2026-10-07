import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Max

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_subtype_gt {A M : Type*} [Fintype A] [LinearOrder A] [AddCommMonoid M]
    (i : A) (f : A → M) :
    (∑ j : {j : A // i < j}, f j.val) = ∑ j, if i < j then f j else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

theorem sum_split_at_layer {A M : Type*} [Fintype A] [LinearOrder A] [AddCommMonoid M]
    (i : A) (f : A → M) :
    (∑ j, f j) = f i + (∑ j, if j < i then f j else 0) +
      ∑ j : {j : A // i < j}, f j.val := by
  classical
  rw [sum_subtype_gt]
  have he (j : A) : f j =
      (if j = i then f j else 0) + (if j < i then f j else 0) +
        (if i < j then f j else 0) := by
    rcases lt_trichotomy j i with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  conv_lhs => arg 2; ext j; rw [he j]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem exists_highest_exceptional_layer {A : Type*} [Fintype A] [LinearOrder A]
    (good : A → Prop) (hbad : ∃ i, ¬good i) :
    ∃ i, ¬good i ∧ ∀ j, i < j → good j := by
  classical
  let bad := Finset.univ.filter (fun i => ¬good i)
  have hne : bad.Nonempty := by
    obtain ⟨i, hi⟩ := hbad
    exact ⟨i, by simp [bad, hi]⟩
  refine ⟨bad.max' hne, (Finset.mem_filter.mp (Finset.max'_mem bad hne)).2, ?_⟩
  intro j hj
  by_contra hn
  have hm : j ∈ bad := by simp [bad, hn]
  exact (not_le_of_gt hj) (Finset.le_max' bad j hm)

end Erdos3

end

end OAI
