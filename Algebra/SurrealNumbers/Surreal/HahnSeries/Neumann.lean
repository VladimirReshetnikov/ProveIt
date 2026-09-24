import Mathlib.Algebra.Group.Submonoid.Pointwise
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Finset.MulAntidiagonal

/-!
# Neumann's support lemma

This file proves both parts of `a:lem:neumann` in
`docs/surcomplex/analysis/article.tex` over an ordered abelian group. The
Neumann monoid of `S` (`a:def:neumannmonoid`) is represented by
`AddSubmonoid.closure S`; Mathlib's `AddSubmonoid.closure_eq_image_sum`
identifies it with the sums of finite words over `S`.

Mathlib supplies well-ordering of sumsets, finite additive antidiagonals, and
well-ordering of the generated monoid. The remaining all-lengths assertion
follows from Higman's lemma: positive words with the same sum form an
antichain under pointwise domination of a subword. In fact, this proves
finiteness of all such words, without requiring them to be nondecreasing.

For a linear order, `Set.IsPWO` is equivalent to `Set.IsWF`; neither a
well-ordered group nor an Archimedean hypothesis is assumed.
-/

namespace Surreal.HahnSeries

open scoped Pointwise

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]

/-- `a:lem:neumann` (a): sumsets of well-ordered sets are well ordered,
and every element has only finitely many representations as a pair sum. -/
theorem neumann_add {S T : Set Γ} (hS : S.IsPWO) (hT : T.IsPWO) :
    (S + T).IsPWO ∧ ∀ g : Γ, (Set.antidiagonal S T g).Finite :=
  ⟨hS.add hT, fun g => Set.AddAntidiagonal.finite_of_isPWO hS hT g⟩

/-- With positive entries in the larger word, domination of a subword
cannot preserve the sum unless the two words are equal. This is the strict
positivity step in the all-lengths argument of `a:lem:neumann` (b). -/
theorem eq_of_sublistForall₂_of_sum_eq {l₁ l₂ : List Γ}
    (h : List.SublistForall₂ (· ≤ ·) l₁ l₂)
    (hpos : ∀ a ∈ l₂, 0 < a) (hsum : l₁.sum = l₂.sum) : l₁ = l₂ := by
  revert hpos hsum
  induction h with
  | @nil l =>
    intro hpos hsum
    cases l with
    | nil => rfl
    | cons a l =>
      have ha : 0 < a := hpos a (List.mem_cons_self)
      have hl : 0 ≤ l.sum :=
        List.sum_nonneg fun b hb => (hpos b (List.mem_cons_of_mem a hb)).le
      have hstrict : 0 < (a :: l).sum := by
        simpa only [List.sum_cons] using add_pos_of_pos_of_nonneg ha hl
      exact False.elim (hstrict.ne hsum)
  | @cons a b l₁ l₂ hab h ih =>
    intro hpos hsum
    have htail : ∀ c ∈ l₂, 0 < c := fun c hc => hpos c (List.mem_cons_of_mem b hc)
    have hle : l₁.sum ≤ l₂.sum := h.sum_le_sum fun c hc => (htail c hc).le
    simp only [List.sum_cons] at hsum
    have hsmall : b + l₁.sum ≤ b + l₂.sum := add_le_add le_rfl hle
    have hba : b ≤ a := (add_le_add_iff_right l₁.sum).mp (hsmall.trans_eq hsum.symm)
    have heq : a = b := le_antisymm hab hba
    subst b
    exact congrArg (List.cons a) (ih htail (add_left_cancel hsum))
  | @cons_right a l₁ l₂ h _ =>
    intro hpos hsum
    have ha : 0 < a := hpos a List.mem_cons_self
    have hle : l₁.sum ≤ l₂.sum :=
      h.sum_le_sum fun b hb => (hpos b (List.mem_cons_of_mem a hb)).le
    have hstrict : l₁.sum < (a :: l₂).sum :=
      hle.trans_lt (lt_add_of_pos_left l₂.sum ha)
    exact False.elim (hstrict.ne hsum)

/-- The all-lengths conclusion of `a:lem:neumann` (b), strengthened to all
finite words. At a fixed exponent, finitely many words over a positive
well-ordered alphabet contribute, counting every possible length together. -/
theorem finite_words_of_sum_eq {S : Set Γ} (hS : S.IsPWO)
    (hpos : ∀ a ∈ S, 0 < a) (g : Γ) :
    {l : List Γ | (∀ a ∈ l, a ∈ S) ∧ l.sum = g}.Finite := by
  have hpwo :
      {l : List Γ | (∀ a ∈ l, a ∈ S) ∧ l.sum = g}.PartiallyWellOrderedOn
        (List.SublistForall₂ (· ≤ ·)) :=
    (hS.partiallyWellOrderedOn_sublistForall₂ (· ≤ ·)).mono fun _ hl => hl.1
  apply IsAntichain.finite_of_partiallyWellOrderedOn ?_ hpwo
  intro l hl m hm hne hrel
  exact hne (eq_of_sublistForall₂_of_sum_eq hrel
    (fun a ha => hpos a (hm.1 a ha)) (hl.2.trans hm.2.symm))

/-- The nondecreasing-word formulation in `a:lem:neumann` (b), obtained
by restricting the stronger all-words finiteness theorem. -/
theorem finite_nondecreasing_words_of_sum_eq {S : Set Γ} (hS : S.IsPWO)
    (hpos : ∀ a ∈ S, 0 < a) (g : Γ) :
    {l : List Γ | (∀ a ∈ l, a ∈ S) ∧ l.Pairwise (· ≤ ·) ∧ l.sum = g}.Finite :=
  (finite_words_of_sum_eq hS hpos g).subset fun _ hl => ⟨hl.1, hl.2.2⟩

/-- Full `a:lem:neumann` (b): the positive Neumann monoid is well ordered,
and the collection of nondecreasing words representing any exponent is
finite across all word lengths. Strict positivity is essential to the
finiteness conclusion. -/
theorem neumann_positive {S : Set Γ} (hS : S.IsPWO) (hpos : ∀ a ∈ S, 0 < a) :
    (AddSubmonoid.closure S : Set Γ).IsPWO ∧
      ∀ g : Γ,
        {l : List Γ | (∀ a ∈ l, a ∈ S) ∧ l.Pairwise (· ≤ ·) ∧ l.sum = g}.Finite :=
  ⟨Set.IsPWO.addSubmonoid_closure (fun a ha => (hpos a ha).le) hS,
    finite_nondecreasing_words_of_sum_eq hS hpos⟩

end Surreal.HahnSeries
