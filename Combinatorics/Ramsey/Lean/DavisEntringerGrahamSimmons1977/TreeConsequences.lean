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

def blockMidpointFree (B : Block) : Prop :=
  ∀ i j k : Fin B.length, (i : Nat) < j → (j : Nat) < k →
    B.get i + B.get k ≠ 2 * B.get j

def blockMidpointFreeDecidable (B : Block) : Decidable (blockMidpointFree B) := by
  unfold blockMidpointFree
  exact Fintype.decidableForallFintype

def blockMidpointFreeCheck (B : Block) : Bool :=
  @decide (blockMidpointFree B) (blockMidpointFreeDecidable B)

@[simp] theorem blockMidpointFreeCheck_eq_true (B : Block) :
    blockMidpointFreeCheck B = true ↔ blockMidpointFree B := by
  simp [blockMidpointFreeCheck]

theorem blockAPFree_three_of_midpointFree {B : Block}
    (hmid : blockMidpointFree B) : BlockAPFree B 3 := by
  intro hap
  obtain ⟨pos, hpos, a, d, hd, hvalues⟩ := hap
  have h01 : pos 0 < pos 1 := hpos (by decide)
  have h12 : pos 1 < pos 2 := hpos (by decide)
  apply hmid (pos 0) (pos 1) (pos 2) h01 h12
  have h0 := hvalues (0 : Fin 3)
  have h1 := hvalues (1 : Fin 3)
  have h2 := hvalues (2 : Fin 3)
  norm_num [blockSequence] at h0 h1 h2
  simp only [List.get_eq_getElem]
  omega

theorem treeVertex_length_three_le {B : Block} (htree : IsTreeVertex B) :
    3 ≤ B.length := by
  induction htree with
  | root132 => norm_num
  | root213 => norm_num
  | root231 => norm_num
  | root312 => norm_num
  | extend _ _ _ _ _ hlen ih => omega

private theorem value_le_length_of_inSpan {B : Block} {x : Nat}
    (horder : IsIntervalOrdering B 1 B.length) (hlen : 3 ≤ B.length)
    (hspan : InSpanOfOneTwoThree B x) : x ≤ B.length := by
  have hmem (z : Nat) (hz : 1 ≤ z) (hz' : z ≤ B.length) : z ∈ B := by
    rw [← List.mem_toFinset, horder.2, Finset.mem_Icc]
    exact ⟨hz, hz'⟩
  have hidx1 : blockIndex B 1 < B.length :=
    List.idxOf_lt_length_iff.mpr (hmem 1 (by omega) (by omega))
  have hidx2 : blockIndex B 2 < B.length :=
    List.idxOf_lt_length_iff.mpr (hmem 2 (by omega) (by omega))
  have hidx3 : blockIndex B 3 < B.length :=
    List.idxOf_lt_length_iff.mpr (hmem 3 (by omega) (by omega))
  have hxidx : blockIndex B x < B.length := by
    unfold InSpanOfOneTwoThree at hspan
    omega
  have hxmem : x ∈ B := List.idxOf_lt_length_iff.mp hxidx
  have hxIcc : x ∈ Finset.Icc 1 B.length := by
    rw [← horder.2]
    exact List.mem_toFinset.mpr hxmem
  exact (Finset.mem_Icc.mp hxIcc).2

theorem treeIsSpecial_complete_of_intervalOrdering {B : Block}
    (horder : IsIntervalOrdering B 1 B.length) (hlen : 3 ≤ B.length)
    (hspecial : IsSpecialVertex B) : treeIsSpecial B = true := by
  rw [treeIsSpecial, decide_eq_true_eq]
  obtain ⟨a, d, hd, hbase, ha, had, ha2d⟩ := hspecial
  have haBound := value_le_length_of_inSpan horder hlen ha
  have hadBound := value_le_length_of_inSpan horder hlen had
  have ha2dBound := value_le_length_of_inSpan horder hlen ha2d
  let af : Fin (B.length + 1) := ⟨a, by omega⟩
  let df : Fin (B.length + 1) := ⟨d, by omega⟩
  have hadLt : a + d < B.length + 1 := by omega
  have ha2dLt : a + 2 * d < B.length + 1 := by omega
  have hbase' : a ≠ 1 ∨ d ≠ 1 := by
    rcases hbase with ha1 | hd1
    · exact Or.inl (bne_iff_ne.mp ha1)
    · exact Or.inr (bne_iff_ne.mp hd1)
  refine ⟨af, df, hd, hbase', hadLt, ha2dLt, ?_, ?_, ?_⟩
  · simpa [af, InSpanOfOneTwoThree] using ha
  · simpa [af, df, InSpanOfOneTwoThree] using had
  · simpa [af, df, InSpanOfOneTwoThree] using ha2d

theorem treeIsSpecial_false_iff_of_treeVertex {B : Block}
    (htree : IsTreeVertex B) :
    treeIsSpecial B = false ↔ ¬ IsSpecialVertex B := by
  constructor
  · intro hcheck hspecial
    have htrue := treeIsSpecial_complete_of_intervalOrdering
      (treeVertex_interval_ordering htree) (treeVertex_length_three_le htree) hspecial
    rw [hcheck] at htrue
    simp at htrue
  · exact treeIsSpecial_false_of_not_special B

private theorem intervalOrdering_insert_next {B : Block}
    (horder : IsIntervalOrdering B 1 B.length) (i : Nat) (hi : i ≤ B.length) :
    IsIntervalOrdering (B.insertIdx i (B.length + 1)) 1
      (B.insertIdx i (B.length + 1)).length := by
  have hlength : (B.insertIdx i (B.length + 1)).length = B.length + 1 :=
    List.length_insertIdx_of_le_length hi _
  constructor
  · have hnotmem : B.length + 1 ∉ B := by
      rw [← List.mem_toFinset, horder.2, Finset.mem_Icc]
      omega
    have hcons : ((B.length + 1) :: B).Nodup := horder.1.cons hnotmem
    exact (List.perm_insertIdx (B.length + 1) B hi).symm.nodup hcons
  · ext x
    rw [List.mem_toFinset, List.mem_insertIdx hi, Finset.mem_Icc, hlength]
    have hBmem : x ∈ B ↔ 1 ≤ x ∧ x ≤ B.length := by
      rw [← List.mem_toFinset, horder.2, Finset.mem_Icc]
    rw [hBmem]
    omega

def checkedTreePath : Block → List Nat → Block
  | B, [] => B
  | B, i :: is =>
      let B' := B.insertIdx i (B.length + 1)
      checkedTreePath B' is

def checkedTreePathCheck : Block → List Nat → Bool
  | _, [] => true
  | B, i :: is =>
      let B' := B.insertIdx i (B.length + 1)
      decide (i ≤ B.length) && !treeIsSpecial B &&
        blockMidpointFreeCheck B' && checkedTreePathCheck B' is

theorem checkedTreePathCheck_sound {B : Block} {is : List Nat}
    (htree : IsTreeVertex B) (hcheck : checkedTreePathCheck B is = true) :
    IsTreeVertex (checkedTreePath B is) := by
  induction is generalizing B with
  | nil => simpa [checkedTreePath]
  | cons i is ih =>
      simp only [checkedTreePathCheck, Bool.and_eq_true, decide_eq_true_eq,
        blockMidpointFreeCheck_eq_true] at hcheck
      rcases hcheck with ⟨⟨⟨hi, hspecialCheck⟩, hmid⟩, htail⟩
      let B' := B.insertIdx i (B.length + 1)
      have hspecialCheck' : treeIsSpecial B = false :=
        Bool.eq_false_of_not_eq_true' hspecialCheck
      have hspecial : ¬ IsSpecialVertex B :=
        (treeIsSpecial_false_iff_of_treeVertex htree).mp hspecialCheck'
      have horder := intervalOrdering_insert_next
        (treeVertex_interval_ordering htree) i hi
      have hfree : BlockAPFree B' 3 := blockAPFree_three_of_midpointFree hmid
      have hsub : B.Sublist B' := by simp [B']
      have hlength : B'.length = B.length + 1 := by
        simpa [B'] using
          (List.length_insertIdx_of_le_length hi (B.length + 1))
      have htree' : IsTreeVertex B' :=
        IsTreeVertex.extend htree hspecial horder hfree hsub hlength
      exact ih htree' htail

def maximumTreeInsertionPositions : List Nat :=
  [3, 0, 3, 3, 6, 1, 7, 2, 10, 0, 4, 4, 12, 3, 7, 5, 18]

def maximumTreeWitness : Block :=
  checkedTreePath [1, 3, 2] maximumTreeInsertionPositions

theorem maximumTreeWitness_certificate :
    checkedTreePathCheck [1, 3, 2] maximumTreeInsertionPositions = true := by
  native_decide

theorem maximumTreeWitness_isTreeVertex : IsTreeVertex maximumTreeWitness := by
  apply checkedTreePathCheck_sound IsTreeVertex.root132 maximumTreeWitness_certificate

theorem maximumTreeWitness_value : maximumTreeWitness =
    [13, 5, 9, 17, 11, 19, 15, 14, 18, 1, 3, 7, 6, 2, 10, 16, 8, 12, 20, 4] := by
  native_decide

theorem maximumTreeWitness_length : maximumTreeWitness.length = 20 := by
  native_decide

theorem maximumTreeWitness_mem_computedLevel :
    maximumTreeWitness ∈ computedTreeLevel 17 := by
  obtain ⟨k, hlength, hmem⟩ :=
    treeVertex_mem_computedLevel maximumTreeWitness_isTreeVertex
  have hk : k = 17 := by
    rw [maximumTreeWitness_length] at hlength
    omega
  subst k
  exact hmem

theorem computational_tree_exact_maximum :
    (∀ B : Block, IsTreeVertex B → B.length ≤ 20) ∧
      ∃ B : Block, IsTreeVertex B ∧ B.length = 20 := by
  refine ⟨computational_tree_bound_holds, maximumTreeWitness, ?_, ?_⟩
  · exact maximumTreeWitness_isTreeVertex
  · exact maximumTreeWitness_length

theorem computational_tree_bound_seventeen_false :
    ¬ (∀ B : Block, IsTreeVertex B → B.length ≤ 17) := by
  intro hbound
  have := hbound maximumTreeWitness maximumTreeWitness_isTreeVertex
  rw [maximumTreeWitness_length] at this
  omega

end LeanProofs.DavisEntringerGrahamSimmons1977
