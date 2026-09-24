import Mathlib.Order.Atoms
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Powerset

/-!
# Infinite Boolean algebras contain infinite disjoint families

This file proves `meas:lem:boolean` in
`docs/surreal/hahn-valued-measures-and-probability/article.tex`: an infinite
Boolean algebra contains a sequence of pairwise disjoint nonzero elements.

If there are infinitely many atoms, distinct atoms are disjoint. Otherwise the
finitely many atoms have a join `s`. If `s = ⊤`, every element is the join of
the atoms below it, so the algebra would be finite. Hence `sᶜ ≠ ⊥`, and no atom
lies below `sᶜ`; repeatedly splitting off a proper nonzero part of the remainder
produces the disjoint sequence. The case with no atoms is the same argument
starting from `⊤`.
-/

namespace Surreal.BooleanDisjoint

variable {α : Type*} [BooleanAlgebra α]

/-- Below an element with no atoms beneath it, a strictly decreasing chain of
nonzero elements gives a pairwise disjoint sequence of nonzero differences. -/
theorem exists_disjoint_of_atomless_below {c : α} (hc : c ≠ ⊥)
    (hno : ∀ a, IsAtom a → ¬ a ≤ c) :
    ∃ f : ℕ → α, (∀ n, f n ≠ ⊥) ∧ Pairwise (Function.onFun Disjoint f) := by
  have hsplit : ∀ x : {x : α // x ≠ ⊥ ∧ x ≤ c}, ∃ y : {x : α // x ≠ ⊥ ∧ x ≤ c}, y.1 < x.1 := by
    rintro ⟨x, hx0, hxc⟩
    have hna : ¬ IsAtom x := fun ha => hno x ha hxc
    rw [IsAtom, not_and_or, not_not] at hna
    rcases hna with h | h
    · exact absurd h hx0
    · push Not at h
      obtain ⟨y, hyx, hy0⟩ := h
      exact ⟨⟨y, hy0, hyx.le.trans hxc⟩, hyx⟩
  choose g hg using hsplit
  let x : ℕ → {x : α // x ≠ ⊥ ∧ x ≤ c} := fun n => Nat.rec ⟨c, hc, le_rfl⟩ (fun _ y => g y) n
  have hx : ∀ n, (x (n + 1)).1 < (x n).1 := fun n => hg (x n)
  have hanti : ∀ m n, m ≤ n → (x n).1 ≤ (x m).1 := by
    intro m n hmn
    induction hmn with
    | refl => exact le_rfl
    | step _ ih => exact (hx _).le.trans ih
  refine ⟨fun n => (x n).1 \ (x (n + 1)).1, fun n => ?_, fun m n hmn => ?_⟩
  · exact fun h => (hx n).not_ge (sdiff_eq_bot_iff.mp h)
  · wlog hlt : m < n generalizing m n
    · exact (this n m (Ne.symm hmn) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hmn))).symm
    refine Disjoint.mono_right (sdiff_le.trans (hanti (m + 1) n hlt)) ?_
    exact disjoint_sdiff_self_left

/-- `meas:lem:boolean`: an infinite Boolean algebra contains a sequence of pairwise
disjoint nonzero elements. -/
theorem exists_pairwise_disjoint_ne_bot [Infinite α] :
    ∃ f : ℕ → α, (∀ n, f n ≠ ⊥) ∧ Pairwise (Function.onFun Disjoint f) := by
  classical
  by_cases hinf : {a : α | IsAtom a}.Infinite
  · let e := hinf.natEmbedding
    refine ⟨fun n => (e n).1, fun n => (e n).2.1, fun m n hmn => ?_⟩
    have hne : (e m).1 ≠ (e n).1 := fun h => hmn (e.injective (Subtype.ext h))
    exact IsAtom.disjoint_of_ne (e m).2 (e n).2 hne
  · have hfin : {a : α | IsAtom a}.Finite := Set.not_infinite.mp hinf
    set s := hfin.toFinset.sup id with hs
    by_cases htop : sᶜ = ⊥
    · -- Every element is the join of the atoms below it, so the algebra is finite.
      exfalso
      have hs_top : s = ⊤ := compl_eq_bot.mp htop
      have hrep : ∀ b : α, b = (hfin.toFinset.filter fun a => a ≤ b).sup id := by
        intro b
        calc b = b ⊓ s := by rw [hs_top, inf_top_eq]
          _ = (hfin.toFinset.filter fun a => a ≤ b).sup id := by
            rw [hs, Finset.sup_inf_distrib_left]
            apply le_antisymm
            · refine Finset.sup_le fun a ha => ?_
              have hatom : IsAtom a := hfin.mem_toFinset.mp ha
              rcases hatom.le_iff.mp (inf_le_right : b ⊓ id a ≤ id a) with h | h
              · rw [h]
                exact bot_le
              · have hab : a ≤ b := h ▸ inf_le_left
                rw [h]
                exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨ha, hab⟩)
            · refine Finset.sup_le fun a ha => ?_
              obtain ⟨ha, hab⟩ := Finset.mem_filter.mp ha
              exact le_trans (le_inf hab le_rfl) (Finset.le_sup (f := fun i => b ⊓ id i) ha)
      refine Set.infinite_univ (α := α) ((hfin.toFinset.powerset.finite_toSet.image
        (fun F => F.sup id)).subset fun b _ => ?_)
      exact ⟨_, Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.filter_subset _ _)),
        (hrep b).symm⟩
    · refine exists_disjoint_of_atomless_below htop fun a ha hac => ?_
      have has : a ≤ s := Finset.le_sup (f := id) (hfin.mem_toFinset.mpr ha)
      exact ha.1 (le_bot_iff.mp (by simpa using le_inf has hac))

end Surreal.BooleanDisjoint
