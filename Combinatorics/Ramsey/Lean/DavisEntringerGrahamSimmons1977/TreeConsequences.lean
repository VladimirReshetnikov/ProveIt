import DavisEntringerGrahamSimmons1977.Statements
import Mathlib

/-!
# Checked consequences of the computational tree

This module implements the finite insertion search used in the second proof
of Fact 5.  The executable search is connected to the paper's inductive
`IsTreeVertex` predicate by a soundness proof; a native kernel-checked
calculation then certifies that no vertex has more than 20 entries.
-/

set_option autoImplicit false

open Finset

namespace LeanProofs.DavisEntringerGrahamSimmons1977

/-- Checks whether inserting the new maximum created a 3-term progression. -/
def treeHasThreeAP (B : Block) : Bool :=
  if ht : blockIndex B B.length < B.length then
    let t : Fin B.length := ⟨blockIndex B B.length, ht⟩
    decide (∃ i j : Fin B.length,
      (t < i ∧ i < j ∧ B.get t ≠ B.get i ∧
        B.get t + B.get j = 2 * B.get i) ∨
      (i < j ∧ j < t ∧ B.get i ≠ B.get j ∧
        B.get i + B.get t = 2 * B.get j))
  else false

/-- Checks the bounded witness condition for a special tree vertex. -/
def treeIsSpecial (B : Block) : Bool :=
  let indices : Vector Nat (B.length + 1) :=
    Vector.ofFn fun x => blockIndex B x
  let lo := min (blockIndex B 1) (min (blockIndex B 2) (blockIndex B 3))
  let hi := max (blockIndex B 1) (max (blockIndex B 2) (blockIndex B 3))
  let inSpan (x : Fin (B.length + 1)) : Prop :=
    lo ≤ indices.get x ∧ indices.get x ≤ hi
  decide (∃ a d : Fin (B.length + 1), 0 < (d : Nat) ∧
    ((a : Nat) ≠ 1 ∨ (d : Nat) ≠ 1) ∧
      ∃ (had : (a : Nat) + d < B.length + 1)
        (ha2d : (a : Nat) + 2 * d < B.length + 1),
        inSpan a ∧ inSpan ⟨(a : Nat) + d, had⟩ ∧
          inSpan ⟨(a : Nat) + 2 * d, ha2d⟩)

/-- Every insertion of the next maximum into a block. -/
def treeInsertions (B : Block) : List Block :=
  (List.range (B.length + 1)).map fun i => B.insertIdx i (B.length + 1)

/-- One executable level transition in the paper's tree. -/
def nextTreeLevel (level : List Block) : List Block :=
  (level.filter fun B => !treeIsSpecial B).flatMap fun B =>
    (treeInsertions B).filter fun B' => !treeHasThreeAP B'

/-- The vertices at size `3 + k`, starting from the four roots. -/
def computedTreeLevel : Nat → List Block
  | 0 => [[1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2]]
  | k + 1 => nextTreeLevel (computedTreeLevel k)

theorem treeHasThreeAP_sound (B : Block)
    (hcheck : treeHasThreeAP B = true) : ¬BlockAPFree B 3 := by
  unfold treeHasThreeAP at hcheck
  split at hcheck
  next ht =>
    let t : Fin B.length := ⟨blockIndex B B.length, ht⟩
    have hwitness := of_decide_eq_true hcheck
    obtain ⟨i, j, hleft | hright⟩ := hwitness
    · rcases hleft with ⟨hti, hij, hne, hsum⟩
      intro hfree
      apply hfree
      refine ⟨![t, i, j], ?_, ?_⟩
      · apply Fin.strictMono_iff_lt_succ.mpr
        intro u
        fin_cases u
        · exact hti
        · exact hij
      · refine ⟨B.get t, (B.get i : Int) - B.get t, ?_, ?_⟩
        · apply bne_iff_ne.mpr
          apply sub_ne_zero.mpr
          exact_mod_cast hne.symm
        · intro u
          have hsum' : (B.get t : Int) + B.get j = 2 * B.get i := by
            exact_mod_cast hsum
          simp only [List.get_eq_getElem] at hsum'
          fin_cases u
          · simp [blockSequence]
          · simp [blockSequence]
          · simp [blockSequence]
            ring_nf at hsum' ⊢
            omega
    · rcases hright with ⟨hij, hjt, hne, hsum⟩
      intro hfree
      apply hfree
      refine ⟨![i, j, t], ?_, ?_⟩
      · apply Fin.strictMono_iff_lt_succ.mpr
        intro u
        fin_cases u
        · exact hij
        · exact hjt
      · refine ⟨B.get i, (B.get j : Int) - B.get i, ?_, ?_⟩
        · apply bne_iff_ne.mpr
          apply sub_ne_zero.mpr
          exact_mod_cast hne.symm
        · intro u
          have hsum' : (B.get i : Int) + B.get t = 2 * B.get j := by
            exact_mod_cast hsum
          simp only [List.get_eq_getElem] at hsum'
          fin_cases u
          · simp [blockSequence]
          · simp [blockSequence]
          · simp [blockSequence]
            ring_nf at hsum' ⊢
            omega
  next ht => simp at hcheck

private theorem treeHasThreeAP_false_of_free (B : Block)
    (hfree : BlockAPFree B 3) : treeHasThreeAP B = false := by
  cases hcheck : treeHasThreeAP B with
  | false => rfl
  | true => exact (treeHasThreeAP_sound B hcheck hfree).elim

theorem treeIsSpecial_sound (B : Block)
    (hcheck : treeIsSpecial B = true) : IsSpecialVertex B := by
  rw [treeIsSpecial, decide_eq_true_eq] at hcheck
  obtain ⟨a, d, hd, hbase, had, ha2d, ha, hadSpan, ha2dSpan⟩ := hcheck
  have hbase' : ((a : Nat) != 1) = true ∨ ((d : Nat) != 1) = true := by
    rcases hbase with ha1 | hd1
    · exact Or.inl (bne_iff_ne.mpr ha1)
    · exact Or.inr (bne_iff_ne.mpr hd1)
  refine ⟨(a : Nat), (d : Nat), hd, hbase', ?_, ?_, ?_⟩
  · simpa [InSpanOfOneTwoThree] using ha
  · simpa [InSpanOfOneTwoThree] using hadSpan
  · simpa [InSpanOfOneTwoThree] using ha2dSpan

private theorem treeIsSpecial_false_of_not_special (B : Block)
    (hspecial : ¬IsSpecialVertex B) : treeIsSpecial B = false := by
  cases hcheck : treeIsSpecial B with
  | false => rfl
  | true => exact (hspecial (treeIsSpecial_sound B hcheck)).elim

private theorem sublist_succ_eq_insertIdx {α : Type*} {L L' : List α}
    (hsub : L.Sublist L') (hlen : L'.length = L.length + 1) :
    ∃ i ≤ L.length, ∃ x, L' = L.insertIdx i x := by
  induction hsub with
  | slnil => simp at hlen
  | @cons L L' a hsub ih =>
      have heq : L = L' := hsub.eq_of_length (by simpa using hlen.symm)
      subst L'
      exact ⟨0, Nat.zero_le _, a, rfl⟩
  | @cons_cons L L' a hsub ih =>
      have hlen' : L'.length = L.length + 1 := by simpa using hlen
      obtain ⟨i, hi, x, rfl⟩ := ih hlen'
      exact ⟨i + 1, by simp; omega, x, by simp [List.insertIdx]⟩

private theorem treeVertex_interval_ordering {B : Block}
    (htree : IsTreeVertex B) : IsIntervalOrdering B 1 B.length := by
  induction htree with
  | root132 =>
      constructor
      · norm_num
      · ext x
        simp
        omega
  | root213 =>
      constructor
      · norm_num
      · ext x
        simp
        omega
  | root231 =>
      constructor
      · norm_num
      · ext x
        simp
        omega
  | root312 =>
      constructor
      · norm_num
      · ext x
        simp
        omega
  | extend _ _ horder _ _ _ _ => exact horder

private theorem treeExtension_eq_insert_new {B B' : Block}
    (hB : IsIntervalOrdering B 1 B.length)
    (hB' : IsIntervalOrdering B' 1 B'.length)
    (hsub : B.Sublist B') (hlen : B'.length = B.length + 1) :
    ∃ i ≤ B.length, B' = B.insertIdx i (B.length + 1) := by
  obtain ⟨i, hi, x, hx⟩ := sublist_succ_eq_insertIdx hsub hlen
  have htop : B.length + 1 ∈ B' := by
    rw [← List.mem_toFinset, hB'.2, Finset.mem_Icc]
    omega
  have htop' : B.length + 1 = x ∨ B.length + 1 ∈ B := by
    apply (List.mem_insertIdx hi).mp
    simpa [hx] using htop
  have hnotTop : B.length + 1 ∉ B := by
    rw [← List.mem_toFinset, hB.2]
    simp
  have hxeq : x = B.length + 1 := by
    rcases htop' with h | h
    · exact h.symm
    · exact (hnotTop h).elim
  subst x
  exact ⟨i, hi, hx⟩

theorem treeVertex_mem_computedLevel {B : Block}
    (htree : IsTreeVertex B) :
    ∃ k : Nat, B.length = 3 + k ∧ B ∈ computedTreeLevel k := by
  induction htree with
  | root132 => exact ⟨0, rfl, by simp [computedTreeLevel]⟩
  | root213 => exact ⟨0, rfl, by simp [computedTreeLevel]⟩
  | root231 => exact ⟨0, rfl, by simp [computedTreeLevel]⟩
  | root312 => exact ⟨0, rfl, by simp [computedTreeLevel]⟩
  | @extend B B' htree hnonspecial horder hfree hsub hlen ih =>
      obtain ⟨k, hlength, hmem⟩ := ih
      obtain ⟨i, hi, hinsert⟩ := treeExtension_eq_insert_new
        (treeVertex_interval_ordering htree) horder hsub hlen
      have hspecialCheck : treeIsSpecial B = false :=
        treeIsSpecial_false_of_not_special B hnonspecial
      have hapCheck : treeHasThreeAP B' = false :=
        treeHasThreeAP_false_of_free B' hfree
      have hinsertion : B' ∈ treeInsertions B := by
        rw [hinsert]
        simp [treeInsertions]
        exact ⟨i, by omega, rfl⟩
      refine ⟨k + 1, by omega, ?_⟩
      rw [computedTreeLevel]
      simp only [nextTreeLevel, List.mem_flatMap]
      refine ⟨B, ?_, ?_⟩
      · exact List.mem_filter.mpr ⟨hmem, by simp [hspecialCheck]⟩
      · exact List.mem_filter.mpr ⟨hinsertion, by simp [hapCheck]⟩

theorem computedTreeLevel_eighteen_empty :
    computedTreeLevel 18 = [] := by native_decide

private theorem computedTreeLevel_empty_of_eighteen_le (k : Nat) (hk : 18 ≤ k) :
    computedTreeLevel k = [] := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction t with
  | zero => exact computedTreeLevel_eighteen_empty
  | succ t ih => simp [computedTreeLevel, ih, nextTreeLevel]

theorem computational_tree_bound_holds : computational_tree_bound := by
  intro B htree
  obtain ⟨k, hlength, hmem⟩ := treeVertex_mem_computedLevel htree
  by_contra hbound
  have hk : 18 ≤ k := by omega
  rw [computedTreeLevel_empty_of_eighteen_le k hk] at hmem
  simp at hmem

end LeanProofs.DavisEntringerGrahamSimmons1977
