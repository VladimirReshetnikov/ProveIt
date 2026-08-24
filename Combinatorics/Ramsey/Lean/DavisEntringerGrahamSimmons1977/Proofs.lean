import DavisEntringerGrahamSimmons1977.Statements
import Mathlib.Data.List.NodupEquivFin
import RamseyPaperCommon.CountConsequences

/-!
# Proofs for Davis--Entringer--Graham--Simmons (1977)

This file proves the assertions catalogued in `Statements.lean`, in source and
dependency order.  Questions explicitly left open in the paper are not
promoted to theorems here.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.DavisEntringerGrahamSimmons1977

/-! ## Permutations of finite intervals -/

theorem deletion_preserves_ap_freeness_holds :
    deletion_preserves_ap_freeness := by
  intro A B k hBA hA hB
  apply hA
  obtain ⟨f, hf⟩ :=
    List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hBA
  obtain ⟨pos, hpos, a, d, hd, hvalues⟩ := hB
  refine ⟨fun i => f (pos i), f.strictMono.comp hpos, a, d, hd, ?_⟩
  intro i
  change blockSequence A (f (pos i)) = _
  rw [show blockSequence A (f (pos i)) = blockSequence B (pos i) by
    simp only [blockSequence]
    exact_mod_cast (hf (pos i)).symm]
  exact hvalues i

private theorem isArithmeticProgression_three_of_affine_two
    (x : Fin 3 → Int) (c : Int)
    (h : IsArithmeticProgression (fun i => 2 * x i + c)) :
    IsArithmeticProgression x := by
  obtain ⟨a, d, hd, hvalues⟩ := h
  have h0 := hvalues (0 : Fin 3)
  have h1 := hvalues (1 : Fin 3)
  have h2 := hvalues (2 : Fin 3)
  norm_num at h0 h1 h2
  refine ⟨x 0, x 1 - x 0, ?_, ?_⟩
  · rw [bne_iff_ne] at hd ⊢
    intro heq
    have : x 1 = x 0 := sub_eq_zero.mp heq
    omega
  · intro i
    fin_cases i
    · simp
    · simp
    · simp
      omega

private theorem intCast_two_mul_sub_one (x : Nat) (hx : 0 < x) :
    ((2 * x - 1 : Nat) : Int) = 2 * (x : Int) - 1 := by
  omega

private theorem blockSequence_twice_append_left (A C : Block)
    (i : Fin (twiceBlock A ++ C).length) (hi : (i : Nat) < A.length) :
    blockSequence (twiceBlock A ++ C) i =
      2 * blockSequence A ⟨i, hi⟩ := by
  simp only [blockSequence, List.get_eq_getElem, twiceBlock]
  rw [List.getElem_append_left (by simpa using hi), List.getElem_map]
  push_cast
  ring

private theorem blockSequence_odd_append_left (A C : Block)
    (hpos : forall x : Nat, x ∈ A → 0 < x)
    (i : Fin ((A.map fun x => 2 * x - 1) ++ C).length)
    (hi : (i : Nat) < A.length) :
    blockSequence ((A.map fun x => 2 * x - 1) ++ C) i =
      2 * blockSequence A ⟨i, hi⟩ - 1 := by
  simp only [blockSequence, List.get_eq_getElem]
  rw [List.getElem_append_left (by simpa using hi), List.getElem_map]
  have hx : 0 < A[i] := hpos A[i] (List.getElem_mem ..)
  exact intCast_two_mul_sub_one _ hx

private theorem blockSequence_twice_append_right (C A : Block)
    (i : Fin (C ++ twiceBlock A).length) (hi : C.length ≤ (i : Nat)) :
    blockSequence (C ++ twiceBlock A) i =
      2 * blockSequence A ⟨(i : Nat) - C.length, by
        have := i.isLt
        simp only [twiceBlock, List.length_append, List.length_map] at this
        omega⟩ := by
  simp only [blockSequence, List.get_eq_getElem, twiceBlock]
  rw [List.getElem_append_right hi, List.getElem_map]
  push_cast
  ring

private theorem blockSequence_odd_append_right (C A : Block)
    (hpos : forall x : Nat, x ∈ A → 0 < x)
    (i : Fin (C ++ (A.map fun x => 2 * x - 1)).length)
    (hi : C.length ≤ (i : Nat)) :
    blockSequence (C ++ (A.map fun x => 2 * x - 1)) i =
      2 * blockSequence A ⟨(i : Nat) - C.length, by
        have := i.isLt
        simp only [List.length_append, List.length_map] at this
        omega⟩ - 1 := by
  simp only [blockSequence, List.get_eq_getElem]
  rw [List.getElem_append_right hi, List.getElem_map]
  have hj : (i : Nat) - C.length < A.length := by
    have := i.isLt
    simp only [List.length_append, List.length_map] at this
    omega
  have hx : 0 < A.get ⟨(i : Nat) - C.length, hj⟩ :=
    hpos (A.get ⟨(i : Nat) - C.length, hj⟩) (List.get_mem ..)
  exact intCast_two_mul_sub_one _ hx

private theorem blockAPFree_parityLift (A A' : Block)
    (_hposA : forall x : Nat, x ∈ A → 0 < x)
    (hposA' : forall x : Nat, x ∈ A' → 0 < x)
    (hfreeA : BlockAPFree A 3) (hfreeA' : BlockAPFree A' 3) :
    BlockAPFree (parityLift A A') 3 := by
  intro hap
  obtain ⟨pos, hpos, hprogression⟩ := hap
  by_cases hp2 : (pos 2 : Nat) < A.length
  · have hbound : forall i : Fin 3, (pos i : Nat) < A.length := by
      intro i
      exact lt_of_le_of_lt (hpos.monotone (Fin.le_last i)) hp2
    let q : Fin 3 → Fin A.length := fun i => ⟨pos i, hbound i⟩
    have hq : StrictMono q := by
      intro i j hij
      change (pos i : Nat) < (pos j : Nat)
      exact hpos hij
    apply hfreeA
    refine ⟨q, hq, isArithmeticProgression_three_of_affine_two
      (fun i => blockSequence A (q i)) 0 ?_⟩
    have heq :
        (fun i => blockSequence (parityLift A A') (pos i)) =
          (fun i => 2 * blockSequence A (q i) + 0) := by
      funext i
      simpa [parityLift, q] using
        blockSequence_twice_append_left A (A'.map fun x => 2 * x - 1)
          (pos i) (hbound i)
    rwa [heq] at hprogression
  · by_cases hp0 : A.length ≤ (pos 0 : Nat)
    · have hlower : forall i : Fin 3, A.length ≤ (pos i : Nat) := by
        intro i
        exact le_trans hp0 (hpos.monotone (Fin.zero_le i))
      have hbound : forall i : Fin 3, (pos i : Nat) - A.length < A'.length := by
        intro i
        have hi : (pos i : Nat) < A.length + A'.length := by
          simpa [parityLift, twiceBlock] using (pos i).isLt
        have hlo := hlower i
        omega
      let q : Fin 3 → Fin A'.length :=
        fun i => ⟨(pos i : Nat) - A.length, hbound i⟩
      have hq : StrictMono q := by
        intro i j hij
        change (pos i : Nat) - A.length < (pos j : Nat) - A.length
        have hpij := hpos hij
        have hi := hlower i
        omega
      apply hfreeA'
      refine ⟨q, hq, isArithmeticProgression_three_of_affine_two
        (fun i => blockSequence A' (q i)) (-1) ?_⟩
      have heq :
          (fun i => blockSequence (parityLift A A') (pos i)) =
            (fun i => 2 * blockSequence A' (q i) + (-1)) := by
        funext i
        simpa [parityLift, q, twiceBlock, sub_eq_add_neg] using
          blockSequence_odd_append_right (twiceBlock A) A' hposA'
            (pos i) (by simpa [twiceBlock] using hlower i)
      rwa [heq] at hprogression
    · have hp0' : (pos 0 : Nat) < A.length := by omega
      have hp2' : A.length ≤ (pos 2 : Nat) := by omega
      obtain ⟨a, d, hd, hvalues⟩ := hprogression
      have h0 := hvalues (0 : Fin 3)
      have h2 := hvalues (2 : Fin 3)
      change blockSequence (twiceBlock A ++ (A'.map fun x => 2 * x - 1)) (pos 0) = _ at h0
      change blockSequence (twiceBlock A ++ (A'.map fun x => 2 * x - 1)) (pos 2) = _ at h2
      norm_num at h0 h2
      rw [blockSequence_twice_append_left A (A'.map fun x => 2 * x - 1)
        (pos 0) hp0'] at h0
      rw [blockSequence_odd_append_right (twiceBlock A) A' hposA'
        (pos 2) (by simpa [twiceBlock] using hp2')] at h2
      omega

private theorem blockAPFree_parityLiftOddFirst (A A' : Block)
    (_hposA : forall x : Nat, x ∈ A → 0 < x)
    (hposA' : forall x : Nat, x ∈ A' → 0 < x)
    (hfreeA : BlockAPFree A 3) (hfreeA' : BlockAPFree A' 3) :
    BlockAPFree (parityLiftOddFirst A A') 3 := by
  intro hap
  obtain ⟨pos, hpos, hprogression⟩ := hap
  by_cases hp2 : (pos 2 : Nat) < A'.length
  · have hbound : forall i : Fin 3, (pos i : Nat) < A'.length := by
      intro i
      exact lt_of_le_of_lt (hpos.monotone (Fin.le_last i)) hp2
    let q : Fin 3 → Fin A'.length := fun i => ⟨pos i, hbound i⟩
    have hq : StrictMono q := by
      intro i j hij
      change (pos i : Nat) < (pos j : Nat)
      exact hpos hij
    apply hfreeA'
    refine ⟨q, hq, isArithmeticProgression_three_of_affine_two
      (fun i => blockSequence A' (q i)) (-1) ?_⟩
    have heq :
        (fun i => blockSequence (parityLiftOddFirst A A') (pos i)) =
          (fun i => 2 * blockSequence A' (q i) + (-1)) := by
      funext i
      simpa [parityLiftOddFirst, q, sub_eq_add_neg] using
        blockSequence_odd_append_left A' (twiceBlock A) hposA'
          (pos i) (hbound i)
    rwa [heq] at hprogression
  · by_cases hp0 : A'.length ≤ (pos 0 : Nat)
    · have hlower : forall i : Fin 3, A'.length ≤ (pos i : Nat) := by
        intro i
        exact le_trans hp0 (hpos.monotone (Fin.zero_le i))
      have hbound : forall i : Fin 3, (pos i : Nat) - A'.length < A.length := by
        intro i
        have hi : (pos i : Nat) < A'.length + A.length := by
          simpa [parityLiftOddFirst, twiceBlock] using (pos i).isLt
        have hlo := hlower i
        omega
      let q : Fin 3 → Fin A.length :=
        fun i => ⟨(pos i : Nat) - A'.length, hbound i⟩
      have hq : StrictMono q := by
        intro i j hij
        change (pos i : Nat) - A'.length < (pos j : Nat) - A'.length
        have hpij := hpos hij
        have hi := hlower i
        omega
      apply hfreeA
      refine ⟨q, hq, isArithmeticProgression_three_of_affine_two
        (fun i => blockSequence A (q i)) 0 ?_⟩
      have heq :
          (fun i => blockSequence (parityLiftOddFirst A A') (pos i)) =
            (fun i => 2 * blockSequence A (q i) + 0) := by
        funext i
        simpa [parityLiftOddFirst, q] using
          blockSequence_twice_append_right (A'.map fun x => 2 * x - 1) A
            (pos i) (by simpa using hlower i)
      rwa [heq] at hprogression
    · have hp0' : (pos 0 : Nat) < A'.length := by omega
      have hp2' : A'.length ≤ (pos 2 : Nat) := by omega
      obtain ⟨a, d, hd, hvalues⟩ := hprogression
      have h0 := hvalues (0 : Fin 3)
      have h2 := hvalues (2 : Fin 3)
      change blockSequence ((A'.map fun x => 2 * x - 1) ++ twiceBlock A) (pos 0) = _ at h0
      change blockSequence ((A'.map fun x => 2 * x - 1) ++ twiceBlock A) (pos 2) = _ at h2
      norm_num at h0 h2
      rw [blockSequence_odd_append_left A' (twiceBlock A) hposA'
        (pos 0) hp0'] at h0
      rw [blockSequence_twice_append_right (A'.map fun x => 2 * x - 1) A
        (pos 2) (by simpa using hp2')] at h2
      omega

theorem parity_construction_is_ap_free_holds :
    parity_construction_is_ap_free := by
  intro A A' hposA hposA' hfreeA hfreeA'
  exact ⟨blockAPFree_parityLift A A' hposA hposA' hfreeA hfreeA',
    blockAPFree_parityLiftOddFirst A A' hposA hposA' hfreeA hfreeA'⟩

private def oneIccEquivFin (n : Nat) :
    {x : Nat // x ∈ Icc 1 n} ≃ Fin n where
  toFun x := ⟨x - 1, by
    have hx := x.property
    simp only [mem_Icc] at hx
    omega⟩
  invFun i := ⟨i + 1, by
    simp only [mem_Icc]
    omega⟩
  left_inv x := by
    apply Subtype.ext
    have hx := x.property
    simp only [mem_Icc] at hx
    dsimp
    omega
  right_inv i := by
    apply Fin.ext
    dsimp

private theorem finiteAPFree_of_intervalBlock (n : Nat) (B : Block)
    (horder : IsIntervalOrdering B 1 n) (hfree : BlockAPFree B 3) :
    exists p : FinitePermutation n, FiniteAPFree p 3 := by
  classical
  have hlen : B.length = n := by
    have hcard := congrArg Finset.card horder.2
    rw [List.toFinset_card_of_nodup horder.1, Nat.card_Icc] at hcard
    omega
  have hset : {x : Nat | x ∈ B} = {x : Nat | x ∈ Icc 1 n} := by
    ext x
    change (x ∈ B) ↔ x ∈ Icc 1 n
    have hx := congrArg (fun s : Finset Nat => x ∈ s) horder.2
    exact Iff.of_eq (by simpa only [List.mem_toFinset] using hx)
  let epos : Fin n ≃ Fin B.length := finCongr hlen.symm
  let emem : Fin B.length ≃ {x : Nat // x ∈ B} := horder.1.getEquiv B
  let esets : {x : Nat // x ∈ B} ≃ {x : Nat // x ∈ Icc 1 n} :=
    Equiv.setCongr hset
  let p : FinitePermutation n := epos.trans (emem.trans (esets.trans (oneIccEquivFin n)))
  have hpvalue (i : Fin n) :
      finitePermutationSequence p i = blockSequence B (epos i) := by
    let x : {x : Nat // x ∈ Icc 1 n} := esets (emem (epos i))
    have hxval : (x : Nat) = B.get (epos i) := by
      rfl
    have hxpos : 1 ≤ (x : Nat) := by
      have hx := x.property
      simp only [mem_Icc] at hx
      exact hx.1
    change (((x : Nat) - 1 + 1 : Nat) : Int) = (B.get (epos i) : Int)
    rw [Nat.sub_add_cancel hxpos, hxval]
  refine ⟨p, ?_⟩
  intro hap
  apply hfree
  obtain ⟨pos, hpos, hprogression⟩ := hap
  refine ⟨fun i => epos (pos i), ?_, ?_⟩
  · intro i j hij
    change (pos i : Nat) < (pos j : Nat)
    exact hpos hij
  · have heq :
        (fun i => finitePermutationSequence p (pos i)) =
          (fun i => blockSequence B (epos (pos i))) := by
      funext i
      exact hpvalue (pos i)
    rwa [heq] at hprogression

private theorem blockAPFree_of_length_lt (B : Block) (k : Nat)
    (hBk : B.length < k) : BlockAPFree B k := by
  rintro ⟨pos, hpos, -⟩
  have hcard := Fintype.card_le_of_injective pos hpos.injective
  simp only [Fintype.card_fin] at hcard
  omega

theorem parity_construction_orders_interval_holds :
    parity_construction_orders_interval := by
  intro m A A' hA hA'
  have hmemA (x : Nat) : x ∈ A ↔ 1 ≤ x ∧ x ≤ m := by
    have h := congrArg (fun s : Finset Nat => x ∈ s) hA.2
    apply Iff.of_eq
    simpa only [List.mem_toFinset, mem_Icc] using h
  have hmemA' (x : Nat) : x ∈ A' ↔ 1 ≤ x ∧ x ≤ m := by
    have h := congrArg (fun s : Finset Nat => x ∈ s) hA'.2
    apply Iff.of_eq
    simpa only [List.mem_toFinset, mem_Icc] using h
  let E := twiceBlock A
  let O := A'.map fun x => 2 * x - 1
  have hE : E.Nodup := by
    apply hA.1.map
    intro x y hxy
    dsimp only [E, twiceBlock] at hxy
    omega
  have hO : O.Nodup := by
    apply hA'.1.map
    intro x y hxy
    dsimp only [O] at hxy
    omega
  have hEO : E.Disjoint O := by
    rw [List.disjoint_left]
    intro z hzE hzO
    simp only [E, twiceBlock, List.mem_map] at hzE
    simp only [O, List.mem_map] at hzO
    obtain ⟨x, hxA, rfl⟩ := hzE
    obtain ⟨y, hyA', hy⟩ := hzO
    have hypos := (hmemA' y).mp hyA'
    omega
  have hEOset : E.toFinset ∪ O.toFinset = Icc 1 (2 * m) := by
    ext z
    simp only [mem_union, List.mem_toFinset, E, O, twiceBlock, List.mem_map, mem_Icc]
    constructor
    · rintro (⟨x, hxA, rfl⟩ | ⟨x, hxA', rfl⟩)
      · have hx := (hmemA x).mp hxA
        omega
      · have hx := (hmemA' x).mp hxA'
        omega
    · intro hz
      by_cases heven : Even z
      · obtain ⟨x, hx⟩ := even_iff_exists_two_mul.mp heven
        left
        refine ⟨x, (hmemA x).mpr ?_, hx.symm⟩
        omega
      · obtain ⟨x, hx⟩ := odd_iff_exists_bit1.mp (Nat.not_even_iff_odd.mp heven)
        right
        refine ⟨x + 1, (hmemA' (x + 1)).mpr ?_, ?_⟩
        · omega
        · omega
  constructor
  · constructor
    · exact hE.append hO hEO
    · simpa only [parityLift, E, O, List.toFinset_append] using hEOset
  · constructor
    · exact hO.append hE hEO.symm
    · simpa only [parityLiftOddFirst, E, O, List.toFinset_append, union_comm] using hEOset

private theorem apFreePowerOfTwoIntervalBlocks :
    forall r : Nat, exists B : Block,
      IsIntervalOrdering B 1 (2 ^ r) ∧ BlockAPFree B 3 := by
  intro r
  induction r with
  | zero =>
      refine ⟨[1], ?_, blockAPFree_of_length_lt [1] 3 (by simp)⟩
      simp [IsIntervalOrdering]
  | succ r ih =>
      obtain ⟨B, horder, hfree⟩ := ih
      have hpos : forall x : Nat, x ∈ B → 0 < x := by
        intro x hx
        have hxset : x ∈ Icc 1 (2 ^ r) := by
          rw [← horder.2]
          simpa only [List.mem_toFinset] using hx
        exact (mem_Icc.mp hxset).1
      have hfreeLift :=
        (parity_construction_is_ap_free_holds B B hpos hpos hfree hfree).1
      have horderLift :=
        (parity_construction_orders_interval_holds (2 ^ r) B B horder horder).1
      refine ⟨parityLift B B, ?_, hfreeLift⟩
      simpa [pow_succ, Nat.mul_comm] using horderLift

private theorem self_le_two_pow : forall n : Nat, n ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpow : 0 < 2 ^ n := pow_pos (by omega) n
      omega

private theorem apFreeIntervalBlock_exists (n : Nat) :
    exists B : Block, IsIntervalOrdering B 1 n ∧ BlockAPFree B 3 := by
  obtain ⟨B, horder, hfree⟩ := apFreePowerOfTwoIntervalBlocks n
  let B' := B.filter fun x => decide (x ≤ n)
  have horder' : IsIntervalOrdering B' 1 n := by
    constructor
    · exact horder.1.filter _
    · simp only [B', List.toFinset_filter]
      ext x
      simp only [mem_filter, horder.2, mem_Icc, decide_eq_true_eq]
      have hnPow := self_le_two_pow n
      omega
  have hfree' : BlockAPFree B' 3 :=
    deletion_preserves_ap_freeness_holds B B' 3 List.filter_sublist hfree
  exact ⟨B', horder', hfree'⟩

theorem finite_ap_free_permutation_exists_holds :
    finite_ap_free_permutation_exists := by
  intro n hn
  obtain ⟨B, horder, hfree⟩ := apFreeIntervalBlock_exists n
  exact finiteAPFree_of_intervalBlock n B horder hfree

theorem initial_count_values_holds : initial_count_values :=
  LeanProofs.RamseyPaperCommon.davis_initial_count_values

theorem table_1_holds : table_1 :=
  LeanProofs.RamseyPaperCommon.davis_table_one

/-! ## Permutations of the positive integers -/

theorem fact_3_increasing_form_holds : fact_3_increasing_form := by
  intro p
  let a : Nat := (p 0 : Nat)
  let witnessValue : PositiveNat := ⟨a + 1, by
    have ha : 0 < a := (p 0).property
    omega⟩
  let witnessIndex : Nat := p.symm witnessValue
  have hwvalue : (p witnessIndex : Nat) = a + 1 := by
    exact congrArg Subtype.val (p.apply_symm_apply witnessValue)
  have hwindex : 0 < witnessIndex := by
    by_contra h
    have hwzero : witnessIndex = 0 := Nat.eq_zero_of_not_pos h
    rw [hwzero] at hwvalue
    have ha : (p 0 : Nat) = a := rfl
    omega
  let P : Nat → Prop := fun i => 0 < i ∧ a < (p i : Nat)
  have hexists : exists i : Nat, P i := by
    exact ⟨witnessIndex, hwindex, by omega⟩
  let j : Nat := Nat.find hexists
  have hj : 0 < j ∧ a < (p j : Nat) := by
    simpa only [j, P] using Nat.find_spec hexists
  let b : Nat := (p j : Nat)
  let delta : Nat := b - a
  have hdelta : 0 < delta := by
    dsimp only [delta, b]
    omega
  let c : Nat := b + delta
  have hcpos : 0 < c := by
    dsimp only [c]
    omega
  let cValue : PositiveNat := ⟨c, hcpos⟩
  let k : Nat := p.symm cValue
  have hkvalue : (p k : Nat) = c := by
    exact congrArg Subtype.val (p.apply_symm_apply cValue)
  have hkpos : 0 < k := by
    by_contra h
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos h
    rw [hkzero] at hkvalue
    have ha : (p 0 : Nat) = a := rfl
    dsimp only [c, delta, b] at hkvalue
    omega
  have hjk : j < k := by
    by_contra h
    have hkj : k ≤ j := Nat.le_of_not_gt h
    rcases hkj.eq_or_lt with hEq | hlt
    · have hb : (p j : Nat) = b := rfl
      rw [hEq] at hkvalue
      dsimp only [c] at hkvalue
      omega
    · have hminimal := Nat.find_min hexists hlt
      apply hminimal
      dsimp only [P]
      refine ⟨hkpos, ?_⟩
      rw [hkvalue]
      dsimp only [c, delta, b]
      omega
  let pos : Fin 3 → Nat := fun i => if i = 0 then 0 else if i = 1 then j else k
  refine ⟨pos, ?_, (a : Int), (delta : Int), ?_, ?_⟩
  · intro i i' hii'
    dsimp only [pos]
    split_ifs <;> omega
  · exact_mod_cast hdelta
  · intro i
    fin_cases i
    · change ((p 0 : Nat) : Int) = (a : Int) + 0 * (delta : Int)
      simp only [zero_mul, add_zero]
      rfl
    · change ((p j : Nat) : Int) = (a : Int) + 1 * (delta : Int)
      have hb : (p j : Nat) = b := rfl
      rw [hb]
      simp only [one_mul]
      dsimp only [delta]
      omega
    · change ((p k : Nat) : Int) = (a : Int) + 2 * (delta : Int)
      rw [hkvalue]
      dsimp only [c, delta, b]
      omega

private theorem hasMonotoneAP_of_hasIncreasingAP {I : Type*} [Preorder I]
    (x : I → Int) (k : Nat) (h : HasIncreasingAP x k) :
    HasMonotoneAP x k := by
  obtain ⟨pos, hpos, a, d, hd, hvalues⟩ := h
  refine ⟨pos, hpos, a, d, ?_, hvalues⟩
  rw [bne_iff_ne]
  omega

theorem fact_3_holds : fact_3 := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  exact hp (hasMonotoneAP_of_hasIncreasingAP (singlyPermutationSequence p) 3
    (fact_3_increasing_form_holds p))

private theorem natFindSpecOpaque {Q : Nat → Prop} [DecidablePred Q]
    (h : exists n, Q n) : Q (Nat.find h) :=
  Nat.find_spec h

private theorem natFindMinOpaque {Q : Nat → Prop} [DecidablePred Q]
    (h : exists n, Q n) {m : Nat} (hm : m < Nat.find h) : ¬ Q m :=
  Nat.find_min h hm

private theorem tenAStart_succ (k : Nat) :
    tenAStart (k + 1) = tenAStart k + 2 * 10 ^ k := by
  simp only [tenAStart, sum_range_succ]
  ring

private theorem tenAStart_strictMono : StrictMono tenAStart := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [tenAStart_succ]
  have hpow : 0 < 10 ^ k := pow_pos (by omega) k
  omega

private theorem two_mul_le_tenAStart : forall k : Nat, 2 * k ≤ tenAStart k := by
  intro k
  induction k with
  | zero => simp [tenAStart]
  | succ k ih =>
      rw [tenAStart_succ]
      have hpow : 0 < 10 ^ k := pow_pos (by omega) k
      omega

theorem decimal_intervals_partition_holds : decimal_intervals_partition := by
  constructor
  · intro k
    have hpow : 0 < 10 ^ k := pow_pos (by omega) k
    constructor
    · simp only [tenA, Nat.card_Icc]
      omega
    constructor
    · simp only [tenB, Nat.card_Icc]
      omega
    · rw [Finset.disjoint_left]
      intro x hxA hxB
      simp only [tenA, mem_Icc] at hxA
      simp only [tenB, tenBStart, mem_Icc] at hxB
      omega
  · intro x
    let P : Nat → Prop := fun k => (x : Nat) ≤ tenAStart (k + 1)
    have hexists : exists k : Nat, P k := by
      refine ⟨(x : Nat), ?_⟩
      dsimp only [P]
      have hbound := two_mul_le_tenAStart ((x : Nat) + 1)
      omega
    let k : Nat := Nat.find hexists
    have hupper : (x : Nat) ≤ tenAStart (k + 1) := by
      change P (Nat.find hexists)
      exact natFindSpecOpaque hexists
    have hlower : tenAStart k < (x : Nat) := by
      by_cases hk : k = 0
      · simpa [hk, tenAStart] using x.property
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have hmin := natFindMinOpaque hexists (show k - 1 < k by omega)
        dsimp only [P] at hmin
        have hpred : k - 1 + 1 = k := by omega
        rw [hpred] at hmin
        omega
    have hscale : tenAStart (k + 1) = tenAStart k + 2 * 10 ^ k :=
      tenAStart_succ k
    dsimp only [k] at hupper hlower hscale
    let flag : Bool := decide ((x : Nat) ≤ tenAStart k + 10 ^ k)
    refine ⟨⟨k, flag⟩, ?_, ?_⟩
    · by_cases hmid : (x : Nat) ≤ tenAStart k + 10 ^ k
      · dsimp only [k] at hmid
        simp [flag, k, hmid, tenA, mem_Icc]
        omega
      · dsimp only [k] at hmid
        simp [flag, k, hmid, tenB, tenBStart, mem_Icc]
        omega
    · intro q hq
      rcases q with ⟨l, qflag⟩
      have hscale' : tenAStart (l + 1) = tenAStart l + 2 * 10 ^ l :=
        tenAStart_succ l
      have hqbounds : tenAStart l < (x : Nat) ∧ (x : Nat) ≤ tenAStart (l + 1) := by
        rw [hscale']
        cases qflag <;> simp [tenA, tenB, tenBStart, mem_Icc] at hq <;> omega
      have hlkFind : l = Nat.find hexists := by
        rcases lt_trichotomy l (Nat.find hexists) with hlk | hlk | hkl
        · have hmono := tenAStart_strictMono.monotone
            (show l + 1 ≤ Nat.find hexists by omega)
          omega
        · exact hlk
        · have hmono := tenAStart_strictMono.monotone
            (show Nat.find hexists + 1 ≤ l by omega)
          omega
      have hlk : l = k := by
        simpa only [k] using hlkFind
      subst l
      dsimp only [k] at hq
      by_cases hmid : (x : Nat) ≤ tenAStart k + 10 ^ k
      · have hflag : flag = true := by simp [flag, hmid]
        rw [← hlk] at hmid
        cases qflag
        · simp [tenB, tenBStart, mem_Icc] at hq
          omega
        · exact Prod.ext hlk hflag.symm
      · have hflag : flag = false := by simp [flag, hmid]
        rw [← hlk] at hmid
        cases qflag
        · exact Prod.ext hlk hflag.symm
        · simp [tenA, mem_Icc] at hq
          omega

private def shiftBlock (s : Nat) (B : Block) : Block :=
  B.map fun x => s + x

private theorem isArithmeticProgression_of_add_const {k : Nat}
    (x : Fin k → Int) (c : Int)
    (h : IsArithmeticProgression (fun i => c + x i)) :
    IsArithmeticProgression x := by
  obtain ⟨a, d, hd, hvalues⟩ := h
  refine ⟨a - c, d, hd, ?_⟩
  intro i
  have hi := hvalues i
  change c + x i = a + (i : Nat) * d at hi
  omega

private theorem shiftBlock_interval_ordering (s n : Nat) (B : Block)
    (hB : IsIntervalOrdering B 1 n) :
    IsIntervalOrdering (shiftBlock s B) (s + 1) (s + n) := by
  constructor
  · apply hB.1.map
    intro x y hxy
    change s + x = s + y at hxy
    omega
  · ext x
    simp only [shiftBlock, List.mem_toFinset, List.mem_map, mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : 1 ≤ y ∧ y ≤ n := by
        have hmem := congrArg (fun t : Finset Nat => y ∈ t) hB.2
        exact (Iff.of_eq (by simpa only [List.mem_toFinset, mem_Icc] using hmem)).mp hy
      omega
    · intro hx
      refine ⟨x - s, ?_, by omega⟩
      have hmem : x - s ∈ Icc 1 n := by
        simp only [mem_Icc]
        omega
      rw [← hB.2] at hmem
      simpa only [List.mem_toFinset] using hmem

private theorem shiftBlock_ap_free (s : Nat) (B : Block)
    (hB : BlockAPFree B 3) : BlockAPFree (shiftBlock s B) 3 := by
  intro hap
  apply hB
  obtain ⟨pos, hpos, hprogression⟩ := hap
  let q : Fin 3 → Fin B.length := fun i => ⟨pos i, by
    simpa only [shiftBlock, List.length_map] using (pos i).isLt⟩
  have hq : StrictMono q := by
    intro i j hij
    change (pos i : Nat) < (pos j : Nat)
    exact hpos hij
  refine ⟨q, hq, isArithmeticProgression_of_add_const
    (fun i => blockSequence B (q i)) (s : Int) ?_⟩
  have heq :
      (fun i => blockSequence (shiftBlock s B) (pos i)) =
        (fun i => (s : Int) + blockSequence B (q i)) := by
    funext i
    simp only [shiftBlock, blockSequence, List.get_eq_getElem, List.getElem_map, q]
    push_cast
    ring
  rwa [heq] at hprogression

theorem decimal_block_choices_exist_holds : decimal_block_choices_exist := by
  classical
  choose B hB using fun k : Nat => apFreeIntervalBlock_exists (10 ^ k)
  let choice : Nat → Block × Block := fun k =>
    (shiftBlock (tenAStart k) (B k), shiftBlock (tenBStart k) (B k))
  refine ⟨choice, ?_⟩
  intro k
  dsimp only [choice]
  exact ⟨shiftBlock_interval_ordering (tenAStart k) (10 ^ k) (B k) (hB k).1,
    shiftBlock_ap_free (tenAStart k) (B k) (hB k).2,
    shiftBlock_interval_ordering (tenBStart k) (10 ^ k) (B k) (hB k).1,
    shiftBlock_ap_free (tenBStart k) (B k) (hB k).2⟩

private theorem blockPrefixLength_succ (blocks : Nat → Block) (k : Nat) :
    blockPrefixLength blocks (k + 1) =
      blockPrefixLength blocks k + (blocks k).length := by
  simp [blockPrefixLength, Finset.sum_range_succ]

private theorem index_le_blockPrefixLength (blocks : Nat → Block)
    (hlen : ∀ k, 0 < (blocks k).length) (k : Nat) :
    k ≤ blockPrefixLength blocks k := by
  induction k with
  | zero => simp [blockPrefixLength]
  | succ k ih =>
      rw [blockPrefixLength_succ]
      have hk := hlen k
      omega

private theorem blockPrefixLength_unbounded (blocks : Nat → Block)
    (hlen : ∀ k, 0 < (blocks k).length) (n : Nat) :
    ∃ k, n < blockPrefixLength blocks (k + 1) := by
  refine ⟨n, ?_⟩
  have h := index_le_blockPrefixLength blocks hlen (n + 1)
  omega

private def positionBlock (blocks : Nat → Block)
    (hlen : ∀ k, 0 < (blocks k).length) (n : Nat) : Nat :=
  Nat.find (blockPrefixLength_unbounded blocks hlen n)

private theorem positionBlock_spec (blocks : Nat → Block)
    (hlen : ∀ k, 0 < (blocks k).length) (n : Nat) :
    n < blockPrefixLength blocks (positionBlock blocks hlen n + 1) := by
  exact Nat.find_spec (blockPrefixLength_unbounded blocks hlen n)

private theorem positionBlock_lower (blocks : Nat → Block)
    (hlen : ∀ k, 0 < (blocks k).length) (n : Nat) :
    blockPrefixLength blocks (positionBlock blocks hlen n) ≤ n := by
  by_cases hk : positionBlock blocks hlen n = 0
  · simp [hk, blockPrefixLength]
  · have hkpos : 0 < positionBlock blocks hlen n := Nat.pos_of_ne_zero hk
    have hmin := Nat.find_min (blockPrefixLength_unbounded blocks hlen n)
      (show positionBlock blocks hlen n - 1 < positionBlock blocks hlen n by omega)
    have hpred : positionBlock blocks hlen n - 1 + 1 =
        positionBlock blocks hlen n := by omega
    rw [hpred] at hmin
    omega

private theorem positionBlock_index_lt (blocks : Nat → Block)
    (hlen : ∀ k, 0 < (blocks k).length) (n : Nat) :
    n - blockPrefixLength blocks (positionBlock blocks hlen n) <
      (blocks (positionBlock blocks hlen n)).length := by
  have hu := positionBlock_spec blocks hlen n
  rw [blockPrefixLength_succ] at hu
  have hl := positionBlock_lower blocks hlen n
  omega

private theorem positionBlock_at (blocks : Nat → Block)
    (hlen : ∀ k, 0 < (blocks k).length) (k j : Nat)
    (hj : j < (blocks k).length) :
    positionBlock blocks hlen (blockPrefixLength blocks k + j) = k := by
  apply le_antisymm
  · apply Nat.find_min'
    rw [blockPrefixLength_succ]
    omega
  · by_contra hnot
    have hlt : positionBlock blocks hlen (blockPrefixLength blocks k + j) < k := by
      omega
    have hmono : blockPrefixLength blocks
        (positionBlock blocks hlen (blockPrefixLength blocks k + j) + 1) ≤
        blockPrefixLength blocks k := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.range_mono (by omega)
    have hspec := positionBlock_spec blocks hlen
      (blockPrefixLength blocks k + j)
    omega

private def concatenatedValue (blocks : Nat → Block)
    (hlen : ∀ k, 0 < (blocks k).length) (n : Nat) : Nat :=
  (blocks (positionBlock blocks hlen n)).get
    ⟨n - blockPrefixLength blocks (positionBlock blocks hlen n),
      positionBlock_index_lt blocks hlen n⟩

private theorem concatenatedValue_at (blocks : Nat → Block)
    (hlen : ∀ k, 0 < (blocks k).length) (k j : Nat)
    (hj : j < (blocks k).length) :
    concatenatedValue blocks hlen (blockPrefixLength blocks k + j) =
      (blocks k).get ⟨j, hj⟩ := by
  simp only [concatenatedValue, List.get_eq_getElem]
  simp only [positionBlock_at blocks hlen k j hj, Nat.add_sub_cancel_left]

private theorem singlyBlockConcatenation_exists
    (blocks : Nat → Block)
    (hlen : ∀ k, 0 < (blocks k).length)
    (hnodup : ∀ k, (blocks k).Nodup)
    (hpos : ∀ k x, x ∈ blocks k → 0 < x)
    (howner : ∀ i j x, x ∈ blocks i → x ∈ blocks j → i = j)
    (hcover : ∀ x : PositiveNat, ∃ k, (x : Nat) ∈ blocks k) :
    ∃ p : SinglyInfinitePermutation, IsSinglyBlockConcatenation p blocks := by
  let f : Nat → PositiveNat := fun n =>
    ⟨concatenatedValue blocks hlen n,
      by
        dsimp only [concatenatedValue]
        exact hpos (positionBlock blocks hlen n) _
          (List.get_mem (blocks (positionBlock blocks hlen n))
            ⟨n - blockPrefixLength blocks (positionBlock blocks hlen n),
              positionBlock_index_lt blocks hlen n⟩)⟩
  have hinj : Function.Injective f := by
    intro n m hnm
    have hvalue : concatenatedValue blocks hlen n =
        concatenatedValue blocks hlen m := congrArg Subtype.val hnm
    let kn := positionBlock blocks hlen n
    let km := positionBlock blocks hlen m
    have hnmem : concatenatedValue blocks hlen n ∈ blocks kn := by
      dsimp only [concatenatedValue, kn]
      exact List.get_mem _ _
    have hmmem : concatenatedValue blocks hlen m ∈ blocks km := by
      dsimp only [concatenatedValue, km]
      exact List.get_mem _ _
    have hk : kn = km := howner kn km _ hnmem (hvalue ▸ hmmem)
    let jn : Fin (blocks kn).length :=
      ⟨n - blockPrefixLength blocks kn, positionBlock_index_lt blocks hlen n⟩
    let jm : Fin (blocks km).length :=
      ⟨m - blockPrefixLength blocks km, positionBlock_index_lt blocks hlen m⟩
    have hnidx : (blocks kn).idxOf (concatenatedValue blocks hlen n) = (jn : Nat) := by
      simpa only [jn, concatenatedValue, kn] using List.get_idxOf (hnodup kn) jn
    have hmidx : (blocks km).idxOf (concatenatedValue blocks hlen m) = (jm : Nat) := by
      simpa only [jm, concatenatedValue, km] using List.get_idxOf (hnodup km) jm
    have hjval : n - blockPrefixLength blocks kn =
        m - blockPrefixLength blocks km := by
      change (jn : Nat) = (jm : Nat)
      rw [← hnidx, ← hmidx, hvalue, hk]
    have hnlow := positionBlock_lower blocks hlen n
    have hmlow := positionBlock_lower blocks hlen m
    change blockPrefixLength blocks kn ≤ n at hnlow
    change blockPrefixLength blocks km ≤ m at hmlow
    have hprefix : blockPrefixLength blocks kn = blockPrefixLength blocks km := by
      rw [hk]
    omega
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨k, hx⟩ := hcover x
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hx
    let n := blockPrefixLength blocks k + (j : Nat)
    refine ⟨n, Subtype.ext ?_⟩
    change concatenatedValue blocks hlen n = (x : Nat)
    simpa only [n, concatenatedValue_at blocks hlen k (j : Nat) j.isLt] using hj
  let p : SinglyInfinitePermutation := Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨p, ?_⟩
  intro k j hj
  simp only [singlyPermutationSequence, blockSequence]
  norm_cast
  change concatenatedValue blocks hlen (blockPrefixLength blocks k + j) = _
  exact concatenatedValue_at blocks hlen k j hj

private def tenStreamAddress (i : Nat) : Nat × Bool :=
  (i / 2, if Even i then false else true)

private theorem tenStreamAddress_injective : Function.Injective tenStreamAddress := by
  intro i j hij
  have hscale : i / 2 = j / 2 := congrArg Prod.fst hij
  have hflag : (if Even i then false else true) =
      (if Even j then false else true) := congrArg Prod.snd hij
  by_cases hi : Even i <;> by_cases hj : Even j
  · have hi' := Nat.two_mul_div_two_of_even hi
    have hj' := Nat.two_mul_div_two_of_even hj
    omega
  · simp [hi, hj] at hflag
  · simp [hi, hj] at hflag
  · have hi' := Nat.two_mul_div_two_add_one_of_odd (Nat.not_even_iff_odd.mp hi)
    have hj' := Nat.two_mul_div_two_add_one_of_odd (Nat.not_even_iff_odd.mp hj)
    omega

private theorem tenBlockStream_mem_address
    (choice : Nat → Block × Block) (hchoice : IsTenBlockChoice choice)
    {i x : Nat} (hx : x ∈ tenBlockStream choice i) :
    if (tenStreamAddress i).2 then x ∈ tenA (tenStreamAddress i).1
      else x ∈ tenB (tenStreamAddress i).1 := by
  by_cases hi : Even i
  · have hx' : x ∈ (choice (i / 2)).2 := by
      simpa [tenBlockStream, hi] using hx
    have horder := (hchoice (i / 2)).2.2.1
    have hmem : x ∈ (choice (i / 2)).2.toFinset := by
      simpa only [List.mem_toFinset] using hx'
    rw [horder.2] at hmem
    change x ∈ tenB (i / 2) at hmem
    simpa [tenStreamAddress, hi] using hmem
  · have hx' : x ∈ (choice (i / 2)).1 := by
      simpa [tenBlockStream, hi] using hx
    have horder := (hchoice (i / 2)).1
    have hmem : x ∈ (choice (i / 2)).1.toFinset := by
      simpa only [List.mem_toFinset] using hx'
    rw [horder.2] at hmem
    change x ∈ tenA (i / 2) at hmem
    simpa [tenStreamAddress, hi] using hmem

theorem decimal_concatenation_exists_holds : decimal_concatenation_exists := by
  intro choice hchoice
  let blocks := tenBlockStream choice
  have hlen : ∀ i, 0 < (blocks i).length := by
    intro i
    by_cases hi : Even i
    · have horder := (hchoice (i / 2)).2.2.1
      have hcard := List.toFinset_card_of_nodup horder.1
      rw [horder.2] at hcard
      have hpow : 0 < 10 ^ (i / 2) := pow_pos (by omega) _
      have hBcard := (decimal_intervals_partition_holds.1 (i / 2)).2.1
      have hlength : (choice (i / 2)).2.length = 10 ^ (i / 2) := by
        change (tenB (i / 2)).card = (choice (i / 2)).2.length at hcard
        omega
      change 0 < (tenBlockStream choice i).length
      rw [tenBlockStream, if_pos hi, hlength]
      exact hpow
    · have horder := (hchoice (i / 2)).1
      have hcard := List.toFinset_card_of_nodup horder.1
      rw [horder.2] at hcard
      have hpow : 0 < 10 ^ (i / 2) := pow_pos (by omega) _
      have hAcard := (decimal_intervals_partition_holds.1 (i / 2)).1
      have hlength : (choice (i / 2)).1.length = 10 ^ (i / 2) := by
        change (tenA (i / 2)).card = (choice (i / 2)).1.length at hcard
        omega
      change 0 < (tenBlockStream choice i).length
      rw [tenBlockStream, if_neg hi, hlength]
      exact hpow
  have hnodup : ∀ i, (blocks i).Nodup := by
    intro i
    by_cases hi : Even i
    · simpa [blocks, tenBlockStream, hi] using
        (hchoice (i / 2)).2.2.1.1
    · simpa [blocks, tenBlockStream, hi] using
        (hchoice (i / 2)).1.1
  have hpos : ∀ i x, x ∈ blocks i → 0 < x := by
    intro i x hx
    have haddr := tenBlockStream_mem_address choice hchoice hx
    by_cases hi : Even i
    · have hmem : x ∈ tenB (i / 2) := by
        simpa [tenStreamAddress, hi] using haddr
      simp only [tenB, mem_Icc] at hmem
      omega
    · have hmem : x ∈ tenA (i / 2) := by
        simpa [tenStreamAddress, hi] using haddr
      simp only [tenA, mem_Icc] at hmem
      omega
  have howner : ∀ i j x, x ∈ blocks i → x ∈ blocks j → i = j := by
    intro i j x hxi hxj
    have hxipos : 0 < x := hpos i x hxi
    obtain ⟨q, hq, hunique⟩ := decimal_intervals_partition_holds.2 ⟨x, hxipos⟩
    have hiMem := tenBlockStream_mem_address choice hchoice hxi
    have hjMem := tenBlockStream_mem_address choice hchoice hxj
    have hiq : tenStreamAddress i = q := hunique (tenStreamAddress i) hiMem
    have hjq : tenStreamAddress j = q := hunique (tenStreamAddress j) hjMem
    exact tenStreamAddress_injective (hiq.trans hjq.symm)
  have hcover : ∀ x : PositiveNat, ∃ i, (x : Nat) ∈ blocks i := by
    intro x
    obtain ⟨q, hq, _⟩ := decimal_intervals_partition_holds.2 x
    rcases q with ⟨k, flag⟩
    cases flag
    · have horder := (hchoice k).2.2.1
      refine ⟨2 * k, ?_⟩
      dsimp only [blocks, tenBlockStream]
      have hmem : (x : Nat) ∈ (choice k).2.toFinset := by
        rw [horder.2]
        exact hq
      have heven : Even (2 * k) := ⟨k, by omega⟩
      have hdiv : (2 * k) / 2 = k := by omega
      simpa [tenBlockStream, heven, hdiv] using hmem
    · have horder := (hchoice k).1
      refine ⟨2 * k + 1, ?_⟩
      dsimp only [blocks, tenBlockStream]
      have hmem : (x : Nat) ∈ (choice k).1.toFinset := by
        rw [horder.2]
        exact hq
      have hodd : ¬ Even (2 * k + 1) := by
        exact Nat.not_even_iff_odd.mpr ⟨k, by omega⟩
      have hdiv : (2 * k + 1) / 2 = k := by omega
      simpa [tenBlockStream, hodd, hdiv] using hmem
  exact singlyBlockConcatenation_exists blocks hlen hnodup hpos howner hcover

private theorem positionBlock_mono (blocks : Nat → Block)
    (hlen : ∀ k, 0 < (blocks k).length) :
    Monotone (positionBlock blocks hlen) := by
  intro n m hnm
  by_contra hnot
  have hlt : positionBlock blocks hlen m < positionBlock blocks hlen n := by
    omega
  have hpref : blockPrefixLength blocks (positionBlock blocks hlen m + 1) ≤
      blockPrefixLength blocks (positionBlock blocks hlen n) := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.range_mono (by omega)
  have hm := positionBlock_spec blocks hlen m
  have hn := positionBlock_lower blocks hlen n
  omega

private theorem blockSequence_at_position (blocks : Nat → Block)
    (hlen : ∀ k, 0 < (blocks k).length) (p : SinglyInfinitePermutation)
    (hconcat : IsSinglyBlockConcatenation p blocks) (n : Nat) :
    singlyPermutationSequence p n =
      blockSequence (blocks (positionBlock blocks hlen n))
        ⟨n - blockPrefixLength blocks (positionBlock blocks hlen n),
          positionBlock_index_lt blocks hlen n⟩ := by
  have hlower := positionBlock_lower blocks hlen n
  have hdecomp : blockPrefixLength blocks (positionBlock blocks hlen n) +
      (n - blockPrefixLength blocks (positionBlock blocks hlen n)) = n := by
    omega
  simpa only [hdecomp] using hconcat (positionBlock blocks hlen n)
    (n - blockPrefixLength blocks (positionBlock blocks hlen n))
    (positionBlock_index_lt blocks hlen n)

private theorem value_mem_position_block (blocks : Nat → Block)
    (hlen : ∀ k, 0 < (blocks k).length) (p : SinglyInfinitePermutation)
    (hconcat : IsSinglyBlockConcatenation p blocks) (n : Nat) :
    (p n : Nat) ∈ blocks (positionBlock blocks hlen n) := by
  have hseq := blockSequence_at_position blocks hlen p hconcat n
  have hnat : (p n : Nat) =
      (blocks (positionBlock blocks hlen n)).get
        ⟨n - blockPrefixLength blocks (positionBlock blocks hlen n),
          positionBlock_index_lt blocks hlen n⟩ := by
    have hcast : (((p n : Nat) : Nat) : Int) =
        (((blocks (positionBlock blocks hlen n)).get
          ⟨n - blockPrefixLength blocks (positionBlock blocks hlen n),
            positionBlock_index_lt blocks hlen n⟩ : Nat) : Int) := hseq
    exact_mod_cast hcast
  rw [hnat]
  exact List.get_mem _ _

private theorem tenBlockStream_ap_free
    (choice : Nat → Block × Block) (hchoice : IsTenBlockChoice choice) (i : Nat) :
    BlockAPFree (tenBlockStream choice i) 3 := by
  by_cases hi : Even i
  · simpa [tenBlockStream, hi] using (hchoice (i / 2)).2.2.2
  · simpa [tenBlockStream, hi] using (hchoice (i / 2)).2.1

private theorem tenBlockStream_length_pos
    (choice : Nat → Block × Block) (hchoice : IsTenBlockChoice choice) (i : Nat) :
    0 < (tenBlockStream choice i).length := by
  by_cases hi : Even i
  · have horder := (hchoice (i / 2)).2.2.1
    have hcard := List.toFinset_card_of_nodup horder.1
    rw [horder.2] at hcard
    have hpow : 0 < 10 ^ (i / 2) := pow_pos (by omega) _
    have hBcard := (decimal_intervals_partition_holds.1 (i / 2)).2.1
    have hlength : (choice (i / 2)).2.length = 10 ^ (i / 2) := by
      change (tenB (i / 2)).card = (choice (i / 2)).2.length at hcard
      omega
    rw [tenBlockStream, if_pos hi, hlength]
    exact hpow
  · have horder := (hchoice (i / 2)).1
    have hcard := List.toFinset_card_of_nodup horder.1
    rw [horder.2] at hcard
    have hpow : 0 < 10 ^ (i / 2) := pow_pos (by omega) _
    have hAcard := (decimal_intervals_partition_holds.1 (i / 2)).1
    have hlength : (choice (i / 2)).1.length = 10 ^ (i / 2) := by
      change (tenA (i / 2)).card = (choice (i / 2)).1.length at hcard
      omega
    rw [tenBlockStream, if_neg hi, hlength]
    exact hpow

private theorem tenAStart_lt_pow : ∀ k : Nat, tenAStart k < 10 ^ k := by
  intro k
  induction k with
  | zero => norm_num [tenAStart]
  | succ k ih =>
      rw [tenAStart_succ, Nat.pow_succ]
      have hpow : 0 < 10 ^ k := pow_pos (by omega) k
      omega

private theorem tenBlockStream_mem_B_of_even
    (choice : Nat → Block × Block) (hchoice : IsTenBlockChoice choice)
    {i x : Nat} (hi : Even i) (hx : x ∈ tenBlockStream choice i) :
    x ∈ tenB (i / 2) := by
  have haddr := tenBlockStream_mem_address choice hchoice hx
  simpa [tenStreamAddress, hi] using haddr

private theorem tenBlockStream_mem_A_of_not_even
    (choice : Nat → Block × Block) (hchoice : IsTenBlockChoice choice)
    {i x : Nat} (hi : ¬ Even i) (hx : x ∈ tenBlockStream choice i) :
    x ∈ tenA (i / 2) := by
  have haddr := tenBlockStream_mem_address choice hchoice hx
  simpa [tenStreamAddress, hi] using haddr

private theorem tenBlockStream_mem_union_bounds
    (choice : Nat → Block × Block) (hchoice : IsTenBlockChoice choice)
    {i x : Nat} (hx : x ∈ tenBlockStream choice i) :
    tenAStart (i / 2) < x ∧ x ≤ tenAStart (i / 2 + 1) := by
  by_cases hi : Even i
  · have hmem := tenBlockStream_mem_B_of_even choice hchoice hi hx
    simp only [tenB, tenBStart, mem_Icc] at hmem
    rw [tenAStart_succ]
    omega
  · have hmem := tenBlockStream_mem_A_of_not_even choice hchoice hi hx
    simp only [tenA, mem_Icc] at hmem
    rw [tenAStart_succ]
    have hpow : 0 < 10 ^ (i / 2) := pow_pos (by omega) _
    omega

private theorem tenScale_le_of_lt
    {i j x y : Nat}
    (hx : tenAStart i < x ∧ x ≤ tenAStart (i + 1))
    (hy : tenAStart j < y ∧ y ≤ tenAStart (j + 1))
    (hxy : x < y) : i ≤ j := by
  by_contra hnot
  have hmono := tenAStart_strictMono.monotone (show j + 1 ≤ i by omega)
  omega

private theorem tenBlockStream_same_scale_of_lt_values
    (choice : Nat → Block × Block) (hchoice : IsTenBlockChoice choice)
    {i j x y : Nat} (hij : i ≤ j) (hscale : i / 2 = j / 2)
    (hx : x ∈ tenBlockStream choice i) (hy : y ∈ tenBlockStream choice j)
    (hxy : x < y) : i = j := by
  by_contra hne
  have hij' : i < j := lt_of_le_of_ne hij hne
  have hiForm : 2 * (i / 2) = i := by omega
  have hjForm : 2 * (j / 2) + 1 = j := by omega
  have hiEven : Even i := ⟨i / 2, by omega⟩
  have hjOdd : ¬ Even j := by
    apply Nat.not_even_iff_odd.mpr
    exact ⟨j / 2, by omega⟩
  have hxB := tenBlockStream_mem_B_of_even choice hchoice hiEven hx
  have hyA := tenBlockStream_mem_A_of_not_even choice hchoice hjOdd hy
  simp only [tenB, tenBStart, mem_Icc] at hxB
  simp only [tenA, mem_Icc] at hyA
  rw [hscale] at hxB
  omega

private theorem no_three_consecutive_same_block
    (blocks : Nat → Block) (hlen : ∀ k, 0 < (blocks k).length)
    (hfree : ∀ k, BlockAPFree (blocks k) 3)
    (p : SinglyInfinitePermutation) (hconcat : IsSinglyBlockConcatenation p blocks)
    (pos : Fin 5 → Nat) (hpos : StrictMono pos)
    (hprogression : IsArithmeticProgression (fun i => singlyPermutationSequence p (pos i)))
    (s : Nat) (hs : s + 2 < 5) :
    ¬ (positionBlock blocks hlen (pos ⟨s, by omega⟩) =
          positionBlock blocks hlen (pos ⟨s + 1, by omega⟩) ∧
        positionBlock blocks hlen (pos ⟨s + 1, by omega⟩) =
          positionBlock blocks hlen (pos ⟨s + 2, by omega⟩)) := by
  rintro ⟨hb01, hb12⟩
  let t : Fin 3 → Fin 5 := fun u => ⟨s + (u : Nat), by omega⟩
  let b := positionBlock blocks hlen (pos (t 0))
  have hb : ∀ u : Fin 3, positionBlock blocks hlen (pos (t u)) = b := by
    intro u
    fin_cases u
    · rfl
    · exact hb01.symm
    · exact (hb01.trans hb12).symm
  let q : Fin 3 → Fin (blocks b).length := fun u =>
    ⟨pos (t u) - blockPrefixLength blocks b, by
      have hu := positionBlock_index_lt blocks hlen (pos (t u))
      rw [hb u] at hu
      exact hu⟩
  have ht : StrictMono t := by
    intro u v huv
    change s + (u : Nat) < s + (v : Nat)
    exact Nat.add_lt_add_left huv s
  have hq : StrictMono q := by
    intro u v huv
    change pos (t u) - blockPrefixLength blocks b <
      pos (t v) - blockPrefixLength blocks b
    have huv' := hpos (ht huv)
    have hlower := positionBlock_lower blocks hlen (pos (t u))
    rw [hb u] at hlower
    omega
  apply hfree b
  refine ⟨q, hq, ?_⟩
  obtain ⟨a, d, hd, hvalues⟩ := hprogression
  refine ⟨a + (s : Nat) * d, d, hd, ?_⟩
  intro u
  have hseq := blockSequence_at_position blocks hlen p hconcat (pos (t u))
  have hsame : blockSequence (blocks b) (q u) =
      singlyPermutationSequence p (pos (t u)) := by
    rw [hseq]
    simp only [blockSequence, List.get_eq_getElem, q]
    simp only [hb u]
  change blockSequence (blocks b) (q u) = _
  rw [hsame]
  have hv := hvalues (t u)
  change singlyPermutationSequence p (pos (t u)) =
    a + ((t u : Fin 5) : Nat) * d at hv
  rw [hv]
  change a + ((t u : Fin 5) : Nat) * d =
    a + (s : Nat) * d + (u : Nat) * d
  simp only [t]
  push_cast
  ring

private theorem decimal_decreasing_five_impossible
    (choice : Nat → Block × Block) (p : SinglyInfinitePermutation)
    (hchoice : IsTenBlockChoice choice)
    (hconcat : IsSinglyBlockConcatenation p (tenBlockStream choice))
    (pos : Fin 5 → Nat) (hpos : StrictMono pos)
    (a d : Int) (hd : d != 0)
    (hvalues : ∀ i, singlyPermutationSequence p (pos i) =
      a + (i : Nat) * d) (hdneg : d < 0) : False := by
  let blocks := tenBlockStream choice
  have hlen : ∀ k, 0 < (blocks k).length := by
    intro k
    exact tenBlockStream_length_pos choice hchoice k
  let r : Fin 5 → Nat := fun i => positionBlock blocks hlen (pos i)
  let x : Fin 5 → Nat := fun i => (p (pos i) : Nat)
  have hmem : ∀ i, x i ∈ blocks (r i) := by
    intro i
    have hseq := blockSequence_at_position blocks hlen p hconcat (pos i)
    have hnat : x i = (blocks (r i)).get
        ⟨pos i - blockPrefixLength blocks (r i), by
          exact positionBlock_index_lt blocks hlen (pos i)⟩ := by
      have hcast : ((x i : Nat) : Int) =
          (((blocks (r i)).get
            ⟨pos i - blockPrefixLength blocks (r i), by
              exact positionBlock_index_lt blocks hlen (pos i)⟩ : Nat) : Int) := hseq
      exact_mod_cast hcast
    rw [hnat]
    exact List.get_mem _ _
  have hbounds : ∀ i, tenAStart (r i / 2) < x i ∧
      x i ≤ tenAStart (r i / 2 + 1) := by
    intro i
    exact tenBlockStream_mem_union_bounds choice hchoice (hmem i)
  have hrmono : Monotone r := by
    intro i j hij
    exact positionBlock_mono blocks hlen (hpos.monotone hij)
  have hxanti : StrictAnti x := by
    intro i j hij
    have hi := hvalues i
    have hj := hvalues j
    change ((x i : Nat) : Int) = a + (i : Nat) * d at hi
    change ((x j : Nat) : Int) = a + (j : Nat) * d at hj
    have hij' : (((i : Nat) : Int)) < ((j : Nat) : Int) := by
      exact_mod_cast hij
    have hcast : ((x j : Nat) : Int) < ((x i : Nat) : Int) := by
      nlinarith [hi, hj]
    exact_mod_cast hcast
  have hscale : ∀ i, r i / 2 = r 0 / 2 := by
    intro i
    apply le_antisymm
    · by_cases hi : i = 0
      · simp [hi]
      · exact tenScale_le_of_lt (hbounds i) (hbounds 0)
          (hxanti (Fin.pos_iff_ne_zero.mpr hi))
    · exact Nat.div_le_div_right (hrmono (Fin.zero_le i))
  have hr01 : r 0 ≤ r 1 := hrmono (by decide)
  have hr12 : r 1 ≤ r 2 := hrmono (by decide)
  have hr23 : r 2 ≤ r 3 := hrmono (by decide)
  have hr34 : r 3 ≤ r 4 := hrmono (by decide)
  have hor : (r 0 = r 1 ∧ r 1 = r 2) ∨ (r 2 = r 3 ∧ r 3 = r 4) := by
    have hs1 := hscale 1
    have hs2 := hscale 2
    have hs3 := hscale 3
    have hs4 := hscale 4
    omega
  have hno0 := no_three_consecutive_same_block blocks hlen
    (tenBlockStream_ap_free choice hchoice) p hconcat pos hpos
    ⟨a, d, hd, hvalues⟩ 0 (by omega)
  have hno2 := no_three_consecutive_same_block blocks hlen
    (tenBlockStream_ap_free choice hchoice) p hconcat pos hpos
    ⟨a, d, hd, hvalues⟩ 2 (by omega)
  rcases hor with hor | hor
  · apply hno0
    change r 0 = r 1 ∧ r 1 = r 2
    exact hor
  · apply hno2
    change r 2 = r 3 ∧ r 3 = r 4
    exact hor

private theorem increasing_distinct_scales_arithmetic
    (r x : Fin 5 → Nat) (delta : Nat) (_hdelta : 0 < delta)
    (hformula : ∀ i, x i = x 0 + (i : Nat) * delta)
    (hbounds : ∀ i, tenAStart (r i / 2) < x i ∧
      x i ≤ tenAStart (r i / 2 + 1))
    (h01 : r 0 / 2 < r 1 / 2) (h12 : r 1 / 2 < r 2 / 2)
    (h23 : r 2 / 2 < r 3 / 2) (h34 : r 3 / 2 < r 4 / 2) : False := by
  let k := r 4 / 2
  have hk : 2 ≤ k := by dsimp only [k]; omega
  have hs2 : r 2 / 2 + 2 ≤ k := by dsimp only [k]; omega
  have hstartMono := tenAStart_strictMono.monotone
    (show r 2 / 2 + 1 ≤ k - 1 by omega)
  have hx2Upper : x 2 ≤ tenAStart (k - 1) := by
    exact le_trans (hbounds 2).2 hstartMono
  have hkpred : k - 1 + 1 = k := by omega
  have hstep := tenAStart_succ (k - 1)
  rw [hkpred] at hstep
  have hx4Lower : tenAStart k < x 4 := (hbounds 4).1
  have hpowBound := tenAStart_lt_pow (k - 1)
  have hx1 := hformula 1
  have hx2 := hformula 2
  have hx4 := hformula 4
  norm_num at hx1 hx2 hx4
  have hpow : 10 ^ k = 10 * 10 ^ (k - 1) := by
    conv_lhs => rw [← hkpred, Nat.pow_succ]
    simp only [Nat.mul_comm]
  omega

private theorem increasing_adjacent_pair_impossible
    (choice : Nat → Block × Block) (p : SinglyInfinitePermutation)
    (hchoice : IsTenBlockChoice choice)
    (hconcat : IsSinglyBlockConcatenation p (tenBlockStream choice))
    (pos : Fin 5 → Nat) (hpos : StrictMono pos)
    (a d : Int) (hd : d != 0)
    (hvalues : ∀ i, singlyPermutationSequence p (pos i) =
      a + (i : Nat) * d) (hdpos : 0 < d)
    (s : Nat) (hs : s + 1 < 5)
    (hpairScale :
      positionBlock (tenBlockStream choice)
          (tenBlockStream_length_pos choice hchoice) (pos ⟨s, by omega⟩) / 2 =
        positionBlock (tenBlockStream choice)
          (tenBlockStream_length_pos choice hchoice) (pos ⟨s + 1, hs⟩) / 2) : False := by
  let blocks := tenBlockStream choice
  have hlen : ∀ k, 0 < (blocks k).length :=
    tenBlockStream_length_pos choice hchoice
  let r : Fin 5 → Nat := fun i => positionBlock blocks hlen (pos i)
  let x : Fin 5 → Nat := fun i => (p (pos i) : Nat)
  let delta : Nat := d.toNat
  have hdeltaCast : (delta : Int) = d := Int.toNat_of_nonneg hdpos.le
  have hdelta : 0 < delta := by omega
  have hformula : ∀ i, x i = x 0 + (i : Nat) * delta := by
    intro i
    have hi := hvalues i
    have h0 := hvalues (0 : Fin 5)
    change ((x i : Nat) : Int) = a + (i : Nat) * d at hi
    change ((x 0 : Nat) : Int) = a + 0 * d at h0
    have hcast : ((x i : Nat) : Int) =
        ((x 0 : Nat) : Int) + ((i : Nat) : Int) * (delta : Int) := by
      rw [hi, h0, hdeltaCast]
      ring
    exact_mod_cast hcast
  have hxmono : StrictMono x := by
    intro i j hij
    rw [hformula i, hformula j]
    have hij' : (i : Nat) < (j : Nat) := hij
    nlinarith
  have hmem : ∀ i, x i ∈ blocks (r i) := by
    intro i
    exact value_mem_position_block blocks hlen p hconcat (pos i)
  have hbounds : ∀ i, tenAStart (r i / 2) < x i ∧
      x i ≤ tenAStart (r i / 2 + 1) := by
    intro i
    exact tenBlockStream_mem_union_bounds choice hchoice (hmem i)
  have hrmono : Monotone r := by
    intro i j hij
    exact positionBlock_mono blocks hlen (hpos.monotone hij)
  let u : Fin 5 := ⟨s, by omega⟩
  let v : Fin 5 := ⟨s + 1, hs⟩
  have huv : u < v := by simp [u, v]
  have hpairScale' : r u / 2 = r v / 2 := by
    exact hpairScale
  have hpairBlock : r u = r v :=
    tenBlockStream_same_scale_of_lt_values choice hchoice
      (hrmono huv.le) hpairScale' (hmem u) (hmem v) (hxmono huv)
  let k := r u / 2
  have hstep : x v = x u + delta := by
    rw [hformula v, hformula u]
    simp only [u, v]
    ring
  have hdeltaSmall : delta < 10 ^ k := by
    by_cases heven : Even (r u)
    · have huB := tenBlockStream_mem_B_of_even choice hchoice heven (hmem u)
      have hvB := tenBlockStream_mem_B_of_even choice hchoice (hpairBlock ▸ heven) (hmem v)
      simp only [tenB, tenBStart, Finset.mem_Icc] at huB hvB
      dsimp only [k]
      rw [← hpairScale'] at hvB
      omega
    · have huA := tenBlockStream_mem_A_of_not_even choice hchoice heven (hmem u)
      have hvOdd : ¬ Even (r v) := by simpa only [hpairBlock] using heven
      have hvA := tenBlockStream_mem_A_of_not_even choice hchoice hvOdd (hmem v)
      simp only [tenA, Finset.mem_Icc] at huA hvA
      dsimp only [k]
      rw [← hpairScale'] at hvA
      omega
  have hno (t : Nat) (ht : t + 2 < 5) :=
    no_three_consecutive_same_block blocks hlen
      (tenBlockStream_ap_free choice hchoice) p hconcat pos hpos
      ⟨a, d, hd, hvalues⟩ t ht
  by_cases heven : Even (r u)
  · by_cases hs0 : s = 0
    · subst s
      have hp01 : r 0 = r 1 := by simpa [u, v] using hpairBlock
      have heven0 : Even (r 0) := by simpa [u] using heven
      have hk0 : k = r 0 / 2 := by rfl
      have hdsmall : delta < 10 ^ (r 0 / 2) := by simpa [k, u] using hdeltaSmall
      have hno0 := hno 0 (by omega)
      have hno2 := hno 2 (by omega)
      have hr12ne : r 1 ≠ r 2 := by
        intro hr12
        apply hno0
        change r 0 = r 1 ∧ r 1 = r 2
        exact ⟨hp01, hr12⟩
      have hs12 : r 1 / 2 < r 2 / 2 := by
        have hle : r 1 / 2 ≤ r 2 / 2 :=
          Nat.div_le_div_right (hrmono (show (1 : Fin 5) ≤ 2 by decide))
        rcases hle.eq_or_lt with heq | hlt
        · have hr12 := tenBlockStream_same_scale_of_lt_values choice hchoice
            (hrmono (show (1 : Fin 5) ≤ 2 by decide)) heq
            (hmem 1) (hmem 2) (hxmono (by decide))
          exact (hr12ne hr12).elim
        · exact hlt
      have hx1B := tenBlockStream_mem_B_of_even choice hchoice
        (hp01 ▸ heven0) (hmem 1)
      simp only [tenB, tenBStart, Finset.mem_Icc] at hx1B
      have hx4eq : x 4 = x 1 + 3 * delta := by
        rw [hformula 4, hformula 1]
        norm_num
        ring
      have hstart1 := tenAStart_succ (r 0 / 2)
      have hstart2 := tenAStart_succ (r 0 / 2 + 1)
      have hpowSucc : 10 ^ (r 0 / 2 + 1) = 10 * 10 ^ (r 0 / 2) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_comm]
      have hx4Upper : x 4 < tenAStart (r 0 / 2 + 2) := by
        rw [show r 0 / 2 + 2 = (r 0 / 2 + 1) + 1 by omega, hstart2, hpowSucc]
        rw [← hp01] at hx1B
        rw [hstart1]
        omega
      have hs4Upper : r 4 / 2 < r 0 / 2 + 2 := by
        by_contra hnot
        have hmono := tenAStart_strictMono.monotone
          (show r 0 / 2 + 2 ≤ r 4 / 2 by omega)
        have hx4Lower := (hbounds 4).1
        omega
      have hs23 : r 2 / 2 ≤ r 3 / 2 :=
        Nat.div_le_div_right (hrmono (by decide))
      have hs34 : r 3 / 2 ≤ r 4 / 2 :=
        Nat.div_le_div_right (hrmono (by decide))
      have hs2eq : r 2 / 2 = r 0 / 2 + 1 := by
        rw [← hp01] at hs12
        omega
      have hs3eq : r 3 / 2 = r 0 / 2 + 1 := by omega
      have hs4eq : r 4 / 2 = r 0 / 2 + 1 := by omega
      have hr23 := tenBlockStream_same_scale_of_lt_values choice hchoice
        (hrmono (show (2 : Fin 5) ≤ 3 by decide)) (hs2eq.trans hs3eq.symm)
        (hmem 2) (hmem 3) (hxmono (by decide))
      have hr34 := tenBlockStream_same_scale_of_lt_values choice hchoice
        (hrmono (show (3 : Fin 5) ≤ 4 by decide)) (hs3eq.trans hs4eq.symm)
        (hmem 3) (hmem 4) (hxmono (by decide))
      apply hno2
      change r 2 = r 3 ∧ r 3 = r 4
      exact ⟨hr23, hr34⟩
    · let w : Fin 5 := ⟨s - 1, by omega⟩
      have hwu : w < u := by simp [w, u]; omega
      have hprev : x u = x w + delta := by
        rw [hformula u, hformula w]
        have hsPred : s - 1 + 1 = s := by omega
        change x 0 + s * delta = x 0 + (s - 1) * delta + delta
        conv_lhs => rw [← hsPred]
        ring
      have huB := tenBlockStream_mem_B_of_even choice hchoice heven (hmem u)
      simp only [tenB, tenBStart, Finset.mem_Icc] at huB
      have hxwLower : tenAStart k < x w := by
        have hdsmallu : delta < 10 ^ (r u / 2) := by
          simpa only [k] using hdeltaSmall
        dsimp only [k]
        omega
      have hswle : r w / 2 ≤ k := by
        exact Nat.div_le_div_right (hrmono hwu.le)
      have hsweq : r w / 2 = k := by
        apply le_antisymm hswle
        by_contra hnot
        have hindex : r w / 2 + 1 ≤ k := by omega
        have hmono := tenAStart_strictMono.monotone hindex
        have hxwUpper := (hbounds w).2
        omega
      have hrwu := tenBlockStream_same_scale_of_lt_values choice hchoice
        (hrmono hwu.le) (by simpa only [k] using hsweq)
        (hmem w) (hmem u) (hxmono hwu)
      apply hno (s - 1) (by omega)
      have hsPred : s - 1 + 1 = s := by omega
      have hsNext : s - 1 + 2 = s + 1 := by omega
      constructor
      · simpa only [r, w, u, hsPred] using hrwu
      · simpa only [r, u, v, hsPred, hsNext] using hpairBlock
  · by_cases hs3 : s = 3
    · subst s
      have hp34 : r 3 = r 4 := by simpa [u, v] using hpairBlock
      have hodd3 : ¬ Even (r 3) := by simpa [u] using heven
      have hdsmall : delta < 10 ^ (r 3 / 2) := by simpa [k, u] using hdeltaSmall
      have hkpos : 0 < r 3 / 2 := by
        by_contra hk
        have hk0 : r 3 / 2 = 0 := by omega
        rw [hk0] at hdsmall
        norm_num at hdsmall
        omega
      have hno0 := hno 0 (by omega)
      have hno1 := hno 1 (by omega)
      have hno2 := hno 2 (by omega)
      have hs1le : r 1 / 2 ≤ r 3 / 2 :=
        Nat.div_le_div_right (hrmono (show (1 : Fin 5) ≤ 3 by decide))
      have hs1lt : r 1 / 2 < r 3 / 2 := by
        rcases hs1le.eq_or_lt with heq | hlt
        · have hr13 := tenBlockStream_same_scale_of_lt_values choice hchoice
            (hrmono (show (1 : Fin 5) ≤ 3 by decide)) heq
            (hmem 1) (hmem 3) (hxmono (by decide))
          have hr12 : r 1 = r 2 := le_antisymm
            (hrmono (show (1 : Fin 5) ≤ 2 by decide))
            (by rw [hr13]; exact hrmono (show (2 : Fin 5) ≤ 3 by decide))
          exfalso
          apply hno1
          change r 1 = r 2 ∧ r 2 = r 3
          exact ⟨hr12, hr12.symm.trans hr13⟩
        · exact hlt
      by_cases hs1pred : r 1 / 2 = r 3 / 2 - 1
      · have hs2le : r 2 / 2 ≤ r 3 / 2 :=
          Nat.div_le_div_right (hrmono (show (2 : Fin 5) ≤ 3 by decide))
        have hs12le : r 1 / 2 ≤ r 2 / 2 :=
          Nat.div_le_div_right (hrmono (show (1 : Fin 5) ≤ 2 by decide))
        by_cases hs2top : r 2 / 2 = r 3 / 2
        · have hr23 := tenBlockStream_same_scale_of_lt_values choice hchoice
            (hrmono (show (2 : Fin 5) ≤ 3 by decide)) hs2top
            (hmem 2) (hmem 3) (hxmono (by decide))
          apply hno2
          change r 2 = r 3 ∧ r 3 = r 4
          exact ⟨hr23, hp34⟩
        · have hs2pred : r 2 / 2 = r 3 / 2 - 1 := by omega
          have hr12 := tenBlockStream_same_scale_of_lt_values choice hchoice
            (hrmono (show (1 : Fin 5) ≤ 2 by decide))
            (hs1pred.trans hs2pred.symm) (hmem 1) (hmem 2) (hxmono (by decide))
          have hstep12 : x 2 = x 1 + delta := by
            rw [hformula 2, hformula 1]
            norm_num
            ring
          by_cases heven1 : Even (r 1)
          · have hx1B := tenBlockStream_mem_B_of_even choice hchoice heven1 (hmem 1)
            have hx2B := tenBlockStream_mem_B_of_even choice hchoice
              (hr12 ▸ heven1) (hmem 2)
            simp only [tenB, tenBStart, Finset.mem_Icc] at hx1B hx2B
            have hdsmallPred : delta < 10 ^ (r 1 / 2) := by
              rw [← hr12] at hx2B
              omega
            have hstep01 : x 1 = x 0 + delta := by
              rw [hformula 1, hformula 0]
              norm_num
            have hx0Lower : tenAStart (r 1 / 2) < x 0 := by omega
            have hs0le : r 0 / 2 ≤ r 1 / 2 :=
              Nat.div_le_div_right (hrmono (show (0 : Fin 5) ≤ 1 by decide))
            have hs0eq : r 0 / 2 = r 1 / 2 := by
              apply le_antisymm hs0le
              by_contra hnot
              have hindex : r 0 / 2 + 1 ≤ r 1 / 2 := by omega
              have hmono := tenAStart_strictMono.monotone hindex
              have hx0Upper := (hbounds 0).2
              omega
            have hr01 := tenBlockStream_same_scale_of_lt_values choice hchoice
              (hrmono (show (0 : Fin 5) ≤ 1 by decide)) hs0eq
              (hmem 0) (hmem 1) (hxmono (by decide))
            apply hno0
            change r 0 = r 1 ∧ r 1 = r 2
            exact ⟨hr01, hr12⟩
          · have hx1A := tenBlockStream_mem_A_of_not_even choice hchoice heven1 (hmem 1)
            have heven2 : ¬ Even (r 2) := by simpa only [hr12] using heven1
            have hx2A := tenBlockStream_mem_A_of_not_even choice hchoice heven2 (hmem 2)
            simp only [tenA, Finset.mem_Icc] at hx1A hx2A
            rw [← hr12] at hx2A
            have hdsmallPred : delta < 10 ^ (r 1 / 2) := by
              omega
            have hstep23 : x 3 = x 2 + delta := by
              rw [hformula 3, hformula 2]
              norm_num
              ring
            have hstart := tenAStart_succ (r 1 / 2)
            have hkrel : r 1 / 2 + 1 = r 3 / 2 := by omega
            have hx3Lower : tenAStart (r 1 / 2 + 1) < x 3 := by
              rw [hkrel]
              exact (hbounds 3).1
            rw [hstart] at hx3Lower
            omega
      · have hs1far : r 1 / 2 + 2 ≤ r 3 / 2 := by omega
        have hmono := tenAStart_strictMono.monotone
          (show r 1 / 2 + 1 ≤ r 3 / 2 - 1 by omega)
        have hx1Upper : x 1 ≤ tenAStart (r 3 / 2 - 1) :=
          (hbounds 1).2.trans hmono
        have hkpred : r 3 / 2 - 1 + 1 = r 3 / 2 := by omega
        have hstart := tenAStart_succ (r 3 / 2 - 1)
        rw [hkpred] at hstart
        have hx3Lower := (hbounds 3).1
        have hstep13 : x 3 = x 1 + 2 * delta := by
          rw [hformula 3, hformula 1]
          norm_num
          ring
        have hpowBound := tenAStart_lt_pow (r 3 / 2 - 1)
        have hstep01 : x 1 = x 0 + delta := by
          rw [hformula 1, hformula 0]
          norm_num
        omega
    · have hslt : s < 3 := by omega
      let z : Fin 5 := ⟨s + 2, by omega⟩
      have hvz : v < z := by simp [v, z]
      have hnext : x z = x v + delta := by
        rw [hformula z, hformula v]
        simp only [z, v]
        ring
      have hoddv : ¬ Even (r v) := by simpa only [hpairBlock] using heven
      have hvA := tenBlockStream_mem_A_of_not_even choice hchoice hoddv (hmem v)
      simp only [tenA, Finset.mem_Icc] at hvA
      have hxzUpper : x z < tenAStart (k + 1) := by
        rw [tenAStart_succ]
        dsimp only [k] at hdeltaSmall
        dsimp only [k]
        rw [← hpairScale'] at hvA
        omega
      have hksz : k ≤ r z / 2 := by
        exact Nat.div_le_div_right (hrmono (huv.le.trans hvz.le))
      have hszk : r z / 2 ≤ k := by
        by_contra hnot
        have hmono := tenAStart_strictMono.monotone
          (show k + 1 ≤ r z / 2 by omega)
        have hxzLower := (hbounds z).1
        omega
      have hsz : r z / 2 = k := le_antisymm hszk hksz
      have hvzScale : r v / 2 = r z / 2 := by
        exact hpairScale'.symm.trans (by simpa only [k] using hsz.symm)
      have hrvz := tenBlockStream_same_scale_of_lt_values choice hchoice
        (hrmono hvz.le) hvzScale
        (hmem v) (hmem z) (hxmono hvz)
      apply hno s (by omega)
      change r u = r v ∧ r v = r z
      exact ⟨hpairBlock, hrvz⟩

private theorem decimal_increasing_five_impossible
    (choice : Nat → Block × Block) (p : SinglyInfinitePermutation)
    (hchoice : IsTenBlockChoice choice)
    (hconcat : IsSinglyBlockConcatenation p (tenBlockStream choice))
    (pos : Fin 5 → Nat) (hpos : StrictMono pos)
    (a d : Int) (hd : d != 0)
    (hvalues : ∀ i, singlyPermutationSequence p (pos i) =
      a + (i : Nat) * d) (hdpos : 0 < d) : False := by
  let hlen : ∀ k, 0 < (tenBlockStream choice k).length :=
    tenBlockStream_length_pos choice hchoice
  let r : Fin 5 → Nat := fun i =>
    positionBlock (tenBlockStream choice) hlen (pos i)
  let x : Fin 5 → Nat := fun i => (p (pos i) : Nat)
  let delta : Nat := d.toNat
  have hdeltaCast : (delta : Int) = d := Int.toNat_of_nonneg hdpos.le
  have hdelta : 0 < delta := by omega
  have hformula : ∀ i, x i = x 0 + (i : Nat) * delta := by
    intro i
    have hi := hvalues i
    have h0 := hvalues (0 : Fin 5)
    change ((x i : Nat) : Int) = a + (i : Nat) * d at hi
    change ((x 0 : Nat) : Int) = a + 0 * d at h0
    have hcast : ((x i : Nat) : Int) =
        ((x 0 : Nat) : Int) + ((i : Nat) : Int) * (delta : Int) := by
      rw [hi, h0, hdeltaCast]
      ring
    exact_mod_cast hcast
  have hmem : ∀ i, x i ∈ tenBlockStream choice (r i) := by
    intro i
    exact value_mem_position_block (tenBlockStream choice) hlen p hconcat (pos i)
  have hbounds : ∀ i, tenAStart (r i / 2) < x i ∧
      x i ≤ tenAStart (r i / 2 + 1) := by
    intro i
    exact tenBlockStream_mem_union_bounds choice hchoice (hmem i)
  have hrmono : Monotone r := by
    intro i j hij
    exact positionBlock_mono (tenBlockStream choice) hlen (hpos.monotone hij)
  have hs01 : r 0 / 2 ≤ r 1 / 2 :=
    Nat.div_le_div_right (hrmono (by decide))
  have hs12 : r 1 / 2 ≤ r 2 / 2 :=
    Nat.div_le_div_right (hrmono (by decide))
  have hs23 : r 2 / 2 ≤ r 3 / 2 :=
    Nat.div_le_div_right (hrmono (by decide))
  have hs34 : r 3 / 2 ≤ r 4 / 2 :=
    Nat.div_le_div_right (hrmono (by decide))
  by_cases h01 : r 0 / 2 = r 1 / 2
  · apply increasing_adjacent_pair_impossible choice p hchoice hconcat pos hpos
      a d hd hvalues hdpos 0 (by omega)
    exact h01
  · by_cases h12 : r 1 / 2 = r 2 / 2
    · apply increasing_adjacent_pair_impossible choice p hchoice hconcat pos hpos
        a d hd hvalues hdpos 1 (by omega)
      exact h12
    · by_cases h23 : r 2 / 2 = r 3 / 2
      · apply increasing_adjacent_pair_impossible choice p hchoice hconcat pos hpos
          a d hd hvalues hdpos 2 (by omega)
        exact h23
      · by_cases h34 : r 3 / 2 = r 4 / 2
        · apply increasing_adjacent_pair_impossible choice p hchoice hconcat pos hpos
            a d hd hvalues hdpos 3 (by omega)
          exact h34
        · exact increasing_distinct_scales_arithmetic r x delta hdelta hformula hbounds
            (lt_of_le_of_ne hs01 h01) (lt_of_le_of_ne hs12 h12)
            (lt_of_le_of_ne hs23 h23) (lt_of_le_of_ne hs34 h34)

theorem decimal_construction_avoids_five_holds :
    decimal_construction_avoids_five := by
  intro choice p hchoice hconcat
  change ¬ HasMonotoneAP (singlyPermutationSequence p) 5
  rintro ⟨pos, hpos, a, d, hd, hvalues⟩
  have hdne : d ≠ 0 := bne_iff_ne.mp hd
  rcases lt_or_gt_of_ne hdne with hdneg | hdpos
  · exact decimal_decreasing_five_impossible choice p hchoice hconcat
      pos hpos a d hd hvalues hdneg
  · exact decimal_increasing_five_impossible choice p hchoice hconcat
      pos hpos a d hd hvalues hdpos

theorem fact_4_holds : fact_4 := by
  obtain ⟨choice, hchoice⟩ := decimal_block_choices_exist_holds
  obtain ⟨p, hconcat⟩ := decimal_concatenation_exists_holds choice hchoice
  unfold fact_4
  apply bne_iff_ne.mpr
  exact Set.nonempty_iff_ne_empty.mp
    ⟨p, decimal_construction_avoids_five_holds choice p hchoice hconcat⟩

private theorem blockSequence_reverse (B : Block)
    (i : Fin B.reverse.length) :
    blockSequence B.reverse i =
      blockSequence B ⟨B.length - 1 - (i : Nat), by
        have hi := i.isLt
        simp only [List.length_reverse] at hi
        omega⟩ := by
  simp only [blockSequence, List.get_eq_getElem]
  exact_mod_cast List.getElem_reverse i.isLt

private theorem blockAPFree_reverse (B : Block) (k : Nat)
    (hfree : BlockAPFree B k) : BlockAPFree B.reverse k := by
  intro hap
  apply hfree
  obtain ⟨pos, hpos, a, d, hd, hvalues⟩ := hap
  let q : Fin k → Fin B.length := fun i =>
    ⟨B.length - 1 - (pos (Fin.rev i) : Nat), by
      have hi := (pos (Fin.rev i)).isLt
      simp only [List.length_reverse] at hi
      omega⟩
  have hq : StrictMono q := by
    intro i j hij
    change B.length - 1 - (pos (Fin.rev i) : Nat) <
      B.length - 1 - (pos (Fin.rev j) : Nat)
    have hrev : Fin.rev j < Fin.rev i := Fin.rev_lt_rev.mpr hij
    have hp := hpos hrev
    have hi := (pos (Fin.rev i)).isLt
    simp only [List.length_reverse] at hi
    omega
  refine ⟨q, hq, a + ((k : Nat) - 1) * d, -d, ?_, ?_⟩
  · rw [bne_iff_ne] at hd ⊢
    omega
  · intro i
    have hv := hvalues (Fin.rev i)
    change blockSequence B.reverse (pos (Fin.rev i)) = _ at hv
    rw [blockSequence_reverse] at hv
    change blockSequence B (q i) = _
    rw [hv]
    have hirev : (Fin.rev i : Nat) = k - 1 - (i : Nat) := by
      rw [Fin.val_rev]
      omega
    have hi : (i : Nat) < k := i.isLt
    have hcast : ((k - 1 - (i : Nat) : Nat) : Int) =
        (k : Int) - 1 - (i : Nat) := by
      omega
    rw [hirev, hcast]
    ring

private def addOneBlock (B : Block) : Block :=
  B.map fun x => x + 1

private theorem blockSequence_addOne (B : Block)
    (i : Fin (addOneBlock B).length) :
    blockSequence (addOneBlock B) i =
      blockSequence B ⟨i, by simpa [addOneBlock] using i.isLt⟩ + 1 := by
  simp only [blockSequence, addOneBlock, List.get_eq_getElem,
    List.getElem_map]
  push_cast
  ring

private theorem blockAPFree_addOne (B : Block) (k : Nat)
    (hfree : BlockAPFree B k) : BlockAPFree (addOneBlock B) k := by
  intro hap
  apply hfree
  obtain ⟨pos, hpos, a, d, hd, hvalues⟩ := hap
  let q : Fin k → Fin B.length := fun i =>
    ⟨pos i, by simpa [addOneBlock] using (pos i).isLt⟩
  refine ⟨q, ?_, a - 1, d, hd, ?_⟩
  · intro i j hij
    change (pos i : Nat) < (pos j : Nat)
    exact hpos hij
  · intro i
    have hv := hvalues i
    change blockSequence (addOneBlock B) (pos i) = _ at hv
    rw [blockSequence_addOne] at hv
    change blockSequence B (q i) = _
    linarith

private theorem twiceBlockPlusOne_as_parityOdd (B : Block) :
    twiceBlockPlusOne B = (addOneBlock B).map (fun x => 2 * x - 1) := by
  simp only [twiceBlockPlusOne, addOneBlock, List.map_map]
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp_apply]
  omega

private theorem dyadicParityAPFree (B : Block)
    (hpos : ∀ x : Nat, x ∈ B → 0 < x) (hfree : BlockAPFree B 3) :
    BlockAPFree (twiceBlock B ++ twiceBlockPlusOne B) 3 ∧
      BlockAPFree (twiceBlockPlusOne B ++ twiceBlock B) 3 := by
  have hfreePlus : BlockAPFree (addOneBlock B) 3 :=
    blockAPFree_addOne B 3 hfree
  have hposPlus : ∀ x : Nat, x ∈ addOneBlock B → 0 < x := by
    intro x hx
    simp only [addOneBlock, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    omega
  have h := parity_construction_is_ap_free_holds B (addOneBlock B)
    hpos hposPlus hfree hfreePlus
  rw [parityLift, parityLiftOddFirst, ← twiceBlockPlusOne_as_parityOdd] at h
  exact h

private theorem dyadicParityOrdering (B : Block) (a b : Nat)
    (horder : IsIntervalOrdering B a b) :
    IsIntervalOrdering (twiceBlock B ++ twiceBlockPlusOne B) (2 * a) (2 * b + 1) ∧
      IsIntervalOrdering (twiceBlockPlusOne B ++ twiceBlock B) (2 * a) (2 * b + 1) := by
  let E := twiceBlock B
  let O := twiceBlockPlusOne B
  have hmem (x : Nat) : x ∈ B ↔ a ≤ x ∧ x ≤ b := by
    have h := congrArg (fun s : Finset Nat => x ∈ s) horder.2
    apply Iff.of_eq
    simpa only [List.mem_toFinset, mem_Icc] using h
  have hE : E.Nodup := by
    apply horder.1.map
    intro x y hxy
    dsimp only [E, twiceBlock] at hxy
    omega
  have hO : O.Nodup := by
    apply horder.1.map
    intro x y hxy
    dsimp only [O, twiceBlockPlusOne] at hxy
    omega
  have hEO : E.Disjoint O := by
    rw [List.disjoint_left]
    intro z hzE hzO
    simp only [E, twiceBlock, List.mem_map] at hzE
    simp only [O, twiceBlockPlusOne, List.mem_map] at hzO
    obtain ⟨x, hx, rfl⟩ := hzE
    obtain ⟨y, hy, heq⟩ := hzO
    omega
  have hset : E.toFinset ∪ O.toFinset = Icc (2 * a) (2 * b + 1) := by
    ext z
    simp only [mem_union, List.mem_toFinset, E, O, twiceBlock, twiceBlockPlusOne,
      List.mem_map, mem_Icc]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · have hxb := (hmem x).mp hx
        omega
      · have hxb := (hmem x).mp hx
        omega
    · intro hz
      by_cases heven : Even z
      · obtain ⟨x, hx⟩ := even_iff_exists_two_mul.mp heven
        left
        refine ⟨x, (hmem x).mpr ?_, hx.symm⟩
        omega
      · obtain ⟨x, hx⟩ := odd_iff_exists_bit1.mp (Nat.not_even_iff_odd.mp heven)
        right
        refine ⟨x, (hmem x).mpr ?_, ?_⟩
        · omega
        · omega
  constructor
  · exact ⟨hE.append hO hEO, by
      simpa only [E, O, List.toFinset_append] using hset⟩
  · exact ⟨hO.append hE hEO.symm, by
      simpa only [E, O, List.toFinset_append, union_comm] using hset⟩

theorem dyadic_block_properties_holds : dyadic_block_properties := by
  intro i
  induction i with
  | zero =>
      constructor
      · simp [dyadicBlock, IsIntervalOrdering]
      · intro hap
        obtain ⟨pos, hpos, -⟩ := hap
        have hcard := Fintype.card_le_of_injective pos hpos.injective
        simp only [dyadicBlock, List.length_cons, List.length_nil, zero_add,
          Fintype.card_fin] at hcard
        omega
  | succ i ih =>
      let B : Block := (dyadicBlock i).reverse
      have horderB : IsIntervalOrdering B (2 ^ i) (2 ^ (i + 1) - 1) := by
        constructor
        · exact List.nodup_reverse.mpr ih.1.1
        · simpa only [B, List.toFinset_reverse] using ih.1.2
      have hfreeB : BlockAPFree B 3 := blockAPFree_reverse (dyadicBlock i) 3 ih.2
      have hposB : ∀ x : Nat, x ∈ B → 0 < x := by
        intro x hx
        have hxset : x ∈ Icc (2 ^ i) (2 ^ (i + 1) - 1) := by
          rw [← horderB.2]
          simpa only [List.mem_toFinset] using hx
        have hpow : 0 < 2 ^ i := pow_pos (by omega) i
        exact lt_of_lt_of_le hpow (mem_Icc.mp hxset).1
      have hord := dyadicParityOrdering B (2 ^ i) (2 ^ (i + 1) - 1) horderB
      have hfree := dyadicParityAPFree B hposB hfreeB
      have hleft : 2 * 2 ^ i = 2 ^ (i + 1) := by
        rw [pow_succ]
        ring
      have hright : 2 * (2 ^ (i + 1) - 1) + 1 = 2 ^ (i + 2) - 1 := by
        rw [show i + 2 = (i + 1) + 1 by omega, pow_succ]
        have hpow : 0 < 2 ^ (i + 1) := pow_pos (by omega) (i + 1)
        omega
      rw [hleft, hright] at hord
      change
        IsIntervalOrdering (dyadicBlock (i + 1)) (2 ^ (i + 1))
            (2 ^ (i + 1 + 1) - 1) /\
          BlockAPFree (dyadicBlock (i + 1)) 3
      simp only [dyadicBlock]
      by_cases hi : Even i
      · simp only [if_pos hi]
        constructor
        · simpa only [B, twiceBlock, twiceBlockPlusOne, ← List.map_reverse,
            show i + 1 + 1 = i + 2 by omega] using hord.1
        · simpa only [B, twiceBlock, twiceBlockPlusOne, ← List.map_reverse] using hfree.1
      · simp only [if_neg hi]
        constructor
        · simpa only [B, twiceBlock, twiceBlockPlusOne, ← List.map_reverse,
            show i + 1 + 1 = i + 2 by omega] using hord.2
        · simpa only [B, twiceBlock, twiceBlockPlusOne, ← List.map_reverse] using hfree.2

private theorem doubly_value_at_index (p : DoublyInfinitePermutation)
    (x : PositiveNat) :
    doublyPermutationSequence p (doublyIndex p x) = (x : Nat) := by
  simp only [doublyPermutationSequence, doublyIndex, p.apply_symm_apply]

private theorem positiveAdd_mul_value (a d : PositiveNat) (m : Nat) :
    ((positiveAdd a (m * (d : Nat)) : PositiveNat) : Nat) =
      (a : Nat) + m * (d : Nat) := by
  rfl

private theorem folkman_no_increasing_triple
    (p : DoublyInfinitePermutation) (hp : p ∈ D 3)
    (a d : PositiveNat) (m : Nat) :
    ¬ (doublyIndex p (positiveAdd a (m * (d : Nat))) <
          doublyIndex p (positiveAdd a ((m + 1) * (d : Nat))) /\
        doublyIndex p (positiveAdd a ((m + 1) * (d : Nat))) <
          doublyIndex p (positiveAdd a ((m + 2) * (d : Nat)))) := by
  rintro ⟨h01, h12⟩
  apply hp
  let pos : Fin 3 → Int := fun i =>
    doublyIndex p (positiveAdd a ((m + (i : Nat)) * (d : Nat)))
  refine ⟨pos, ?_, (a : Nat) + m * (d : Nat), (d : Nat), ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · simpa [pos] using h01
    · simpa [pos] using h12
  · rw [bne_iff_ne]
    exact_mod_cast d.property.ne'
  · intro i
    change doublyPermutationSequence p
      (doublyIndex p (positiveAdd a ((m + (i : Nat)) * (d : Nat)))) = _
    rw [doubly_value_at_index]
    simp only [positiveAdd_mul_value]
    push_cast
    ring

private theorem folkman_no_decreasing_triple
    (p : DoublyInfinitePermutation) (hp : p ∈ D 3)
    (a d : PositiveNat) (m : Nat) :
    ¬ (doublyIndex p (positiveAdd a (m * (d : Nat))) >
          doublyIndex p (positiveAdd a ((m + 1) * (d : Nat))) /\
        doublyIndex p (positiveAdd a ((m + 1) * (d : Nat))) >
          doublyIndex p (positiveAdd a ((m + 2) * (d : Nat)))) := by
  rintro ⟨h01, h12⟩
  apply hp
  let pos : Fin 3 → Int := fun i =>
    doublyIndex p (positiveAdd a ((m + (2 - (i : Nat))) * (d : Nat)))
  refine ⟨pos, ?_, (a : Nat) + (m + 2) * (d : Nat), -((d : Nat) : Int), ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · simpa [pos] using h12
    · simpa [pos] using h01
  · rw [bne_iff_ne]
    have hd : (0 : Int) < (d : Nat) := by exact_mod_cast d.property
    omega
  · intro i
    change doublyPermutationSequence p
      (doublyIndex p (positiveAdd a ((m + (2 - (i : Nat))) * (d : Nat)))) = _
    rw [doubly_value_at_index]
    simp only [positiveAdd_mul_value]
    push_cast
    fin_cases i <;> norm_num <;> ring

private theorem folkman_indices_ne
    (p : DoublyInfinitePermutation) (a d : PositiveNat) {m n : Nat}
    (hmn : m ≠ n) :
    doublyIndex p (positiveAdd a (m * (d : Nat))) ≠
      doublyIndex p (positiveAdd a (n * (d : Nat))) := by
  intro hidx
  have hval := congrArg p hidx
  simp only [doublyIndex, p.apply_symm_apply] at hval
  have hnat := congrArg Subtype.val hval
  simp only [positiveAdd] at hnat
  apply hmn
  exact Nat.mul_right_cancel d.property (Nat.add_left_cancel hnat)

private theorem alternates_from_lt (f : Nat → Int)
    (hne : ∀ {m n : Nat}, m ≠ n → f m ≠ f n)
    (hinc : ∀ m : Nat, ¬ (f m < f (m + 1) ∧ f (m + 1) < f (m + 2)))
    (hdec : ∀ m : Nat, ¬ (f m > f (m + 1) ∧ f (m + 1) > f (m + 2)))
    (hstart : f 0 < f 1) :
    ∀ m : Nat, f (2 * m) < f (2 * m + 1) ∧ f (2 * m + 1) > f (2 * m + 2) := by
  intro m
  induction m with
  | zero =>
      constructor
      · simpa using hstart
      · rcases lt_or_gt_of_ne (hne (m := 1) (n := 2) (by omega)) with hlt | hgt
        · exact (hinc 0 ⟨by simpa using hstart, by simpa using hlt⟩).elim
        · simpa using hgt
  | succ m ih =>
      have hprev : f (2 * m + 1) > f (2 * m + 2) := ih.2
      have hfirstNorm : f (2 * m + 2) < f (2 * m + 3) := by
        rcases lt_or_gt_of_ne (hne (m := 2 * m + 2) (n := 2 * m + 3) (by omega)) with
          hlt | hgt
        · exact hlt
        · exact (hdec (2 * m + 1) ⟨by simpa using hprev, by simpa using hgt⟩).elim
      have hsecondNorm : f (2 * m + 3) > f (2 * m + 4) := by
        rcases lt_or_gt_of_ne (hne (m := 2 * m + 3) (n := 2 * m + 4) (by omega)) with
          hlt | hgt
        · exact (hinc (2 * m + 2) ⟨by simpa using hfirstNorm, by simpa using hlt⟩).elim
        · exact hgt
      constructor
      · simpa only [show 2 * (m + 1) = 2 * m + 2 by omega,
          show 2 * (m + 1) + 1 = 2 * m + 3 by omega] using hfirstNorm
      · simpa only [show 2 * (m + 1) + 1 = 2 * m + 3 by omega,
          show 2 * (m + 1) + 2 = 2 * m + 4 by omega] using hsecondNorm

private theorem folkman_alternates_from_lt
    (p : DoublyInfinitePermutation) (hp : p ∈ D 3)
    (a d : PositiveNat)
    (hstart : doublyIndex p a < doublyIndex p (positiveAdd a d)) :
    ∀ m : Nat,
      doublyIndex p (positiveAdd a (2 * m * d)) <
          doublyIndex p (positiveAdd a ((2 * m + 1) * d)) /\
        doublyIndex p (positiveAdd a ((2 * m + 1) * d)) >
          doublyIndex p (positiveAdd a ((2 * m + 2) * d)) := by
  let f : Nat → Int := fun m =>
    doublyIndex p (positiveAdd a (m * (d : Nat)))
  have hf := alternates_from_lt f
    (fun hmn => folkman_indices_ne p a d hmn)
    (folkman_no_increasing_triple p hp a d)
    (folkman_no_decreasing_triple p hp a d)
    (by simpa [f, positiveAdd] using hstart)
  intro m
  simpa only [f, Nat.mul_assoc] using hf m

private theorem alternates_from_gt (f : Nat → Int)
    (hne : ∀ {m n : Nat}, m ≠ n → f m ≠ f n)
    (hinc : ∀ m : Nat, ¬ (f m < f (m + 1) ∧ f (m + 1) < f (m + 2)))
    (hdec : ∀ m : Nat, ¬ (f m > f (m + 1) ∧ f (m + 1) > f (m + 2)))
    (hstart : f 0 > f 1) :
    ∀ m : Nat, f (2 * m) > f (2 * m + 1) ∧ f (2 * m + 1) < f (2 * m + 2) := by
  let g : Nat → Int := fun m => -f m
  have hg : ∀ m : Nat, g (2 * m) < g (2 * m + 1) ∧
      g (2 * m + 1) > g (2 * m + 2) :=
    alternates_from_lt g
      (fun {m n} hmn h => hne hmn (by dsimp only [g] at h; omega))
      (fun m h => hdec m (by dsimp only [g] at h; omega))
      (fun m h => hinc m (by dsimp only [g] at h; omega))
      (by dsimp only [g]; omega)
  intro m
  have := hg m
  dsimp only [g] at this
  omega

private theorem folkman_alternates_from_gt
    (p : DoublyInfinitePermutation) (hp : p ∈ D 3)
    (a d : PositiveNat)
    (hstart : doublyIndex p a > doublyIndex p (positiveAdd a d)) :
    ∀ m : Nat,
      doublyIndex p (positiveAdd a (2 * m * d)) >
          doublyIndex p (positiveAdd a ((2 * m + 1) * d)) /\
        doublyIndex p (positiveAdd a ((2 * m + 1) * d)) <
          doublyIndex p (positiveAdd a ((2 * m + 2) * d)) := by
  let f : Nat → Int := fun m =>
    doublyIndex p (positiveAdd a (m * (d : Nat)))
  have hf := alternates_from_gt f
    (fun hmn => folkman_indices_ne p a d hmn)
    (folkman_no_increasing_triple p hp a d)
    (folkman_no_decreasing_triple p hp a d)
    (by simpa [f, positiveAdd] using hstart)
  intro m
  simpa only [f, Nat.mul_assoc] using hf m

theorem folkman_alternating_order_holds : folkman_alternating_order := by
  intro p hp a d
  constructor
  · constructor
    · exact folkman_alternates_from_lt p hp a d
    · intro h
      have h0 := (h 0).1
      simpa [positiveAdd] using h0
  · constructor
    · exact folkman_alternates_from_gt p hp a d
    · intro h
      have h0 := (h 0).1
      simpa [positiveAdd] using h0

private theorem doubly_indices_ne_of_ne (p : DoublyInfinitePermutation)
    {x y : PositiveNat} (hxy : x ≠ y) :
    doublyIndex p x ≠ doublyIndex p y := by
  intro h
  apply hxy
  simpa only [doublyIndex, p.symm.injective.eq_iff] using h

private theorem folkman_even_pair_reflect_lt
    (p : DoublyInfinitePermutation) (hp : p ∈ D 3)
    (a d : PositiveNat) (m : Nat)
    (hpair :
      doublyIndex p (positiveAdd a (2 * m * d)) <
        doublyIndex p (positiveAdd a ((2 * m + 1) * d))) :
    doublyIndex p a < doublyIndex p (positiveAdd a d) := by
  have hne : doublyIndex p a ≠ doublyIndex p (positiveAdd a d) := by
    apply doubly_indices_ne_of_ne p
    intro heq
    have hval := congrArg Subtype.val heq
    simp only [positiveAdd] at hval
    omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hlt
  · have hcontra := ((folkman_alternating_order_holds p hp a d).2.mp hgt m).1
    omega

private theorem folkman_odd_pair_reflect_lt
    (p : DoublyInfinitePermutation) (hp : p ∈ D 3)
    (a d : PositiveNat) (m : Nat)
    (hpair :
      doublyIndex p (positiveAdd a ((2 * m + 1) * d)) >
        doublyIndex p (positiveAdd a ((2 * m + 2) * d))) :
    doublyIndex p a < doublyIndex p (positiveAdd a d) := by
  have hne : doublyIndex p a ≠ doublyIndex p (positiveAdd a d) := by
    apply doubly_indices_ne_of_ne p
    intro heq
    have hval := congrArg Subtype.val heq
    simp only [positiveAdd] at hval
    omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hlt
  · have hcontra := ((folkman_alternating_order_holds p hp a d).2.mp hgt m).2
    omega

theorem folkman_odd_order_claim_holds : folkman_odd_order_claim := by
  intro p hp hstart
  let one : PositiveNat := ⟨1, by omega⟩
  let two : PositiveNat := ⟨2, by omega⟩
  have hunit (a : PositiveNat) (ha : Odd (a : Nat)) :
      doublyIndex p a < doublyIndex p (positiveAdd a one) := by
    obtain ⟨m, hm⟩ := ha
    have hpair := ((folkman_alternating_order_holds p hp one one).1.mp
      (by
        have htwo : positiveAdd one one = (⟨2, by omega⟩ : PositiveNat) := by
          apply Subtype.ext
          rfl
        rw [htwo]
        simpa only [one] using hstart) m).1
    have hleft : positiveAdd one (2 * m * (one : Nat)) = a := by
      apply Subtype.ext
      dsimp only [positiveAdd, one]
      omega
    have hright : positiveAdd one ((2 * m + 1) * (one : Nat)) =
        positiveAdd a one := by
      apply Subtype.ext
      dsimp only [positiveAdd, one]
      omega
    rwa [hleft, hright] at hpair
  have claim : ∀ k : Nat, ∀ a : PositiveNat, Odd (a : Nat) →
      doublyIndex p a < doublyIndex p (positiveAdd a (2 * k + 1)) := by
    intro k
    induction k with
    | zero =>
        intro a ha
        simpa only [zero_mul, zero_add, one] using hunit a ha
    | succ k ih =>
        intro a ha
        let dn : PositiveNat := ⟨2 * k + 1, by omega⟩
        let dnext : PositiveNat := ⟨2 * (k + 1) + 1, by omega⟩
        let b : PositiveNat := positiveAdd a (2 * (dn : Nat) + 4)
        have hbodd : Odd (b : Nat) := by
          obtain ⟨r, hr⟩ := ha
          refine ⟨r + (dn : Nat) + 2, ?_⟩
          dsimp only [b, positiveAdd]
          omega
        have hbIH : doublyIndex p b < doublyIndex p (positiveAdd b dn) := by
          have h := ih b hbodd
          have hdn : (dn : Nat) = 2 * k + 1 := rfl
          rwa [hdn]
        let c : PositiveNat := positiveAdd b dn
        let c2 : PositiveNat := positiveAdd c two
        have hcne : doublyIndex p c ≠ doublyIndex p c2 := by
          apply doubly_indices_ne_of_ne p
          intro heq
          have hval := congrArg Subtype.val heq
          dsimp only [c2, positiveAdd, two] at hval
          omega
        rcases lt_or_gt_of_ne hcne with hclt | hcgt
        · have hbc2 : doublyIndex p b < doublyIndex p c2 := by
            dsimp only [c] at hclt
            exact hbIH.trans hclt
          have heven : doublyIndex p a < doublyIndex p (positiveAdd a dnext) := by
            apply folkman_even_pair_reflect_lt p hp a dnext 1
            have hleft : positiveAdd a (2 * 1 * (dnext : Nat)) = b := by
              apply Subtype.ext
              dsimp only [positiveAdd, dnext, b, dn]
              omega
            have hright : positiveAdd a ((2 * 1 + 1) * (dnext : Nat)) = c2 := by
              apply Subtype.ext
              dsimp only [positiveAdd, dnext, c2, c, b, dn, two]
              omega
            rwa [hleft, hright]
          have hdnext : (dnext : Nat) = 2 * (k + 1) + 1 := rfl
          rwa [hdnext] at heven
        · have hbasePair :
              doublyIndex p (positiveAdd a dn) <
                doublyIndex p (positiveAdd (positiveAdd a dn) two) := by
            apply folkman_odd_pair_reflect_lt p hp (positiveAdd a dn) two (k + 1)
            have hleft :
                positiveAdd (positiveAdd a dn) ((2 * (k + 1) + 1) * (two : Nat)) = c := by
              apply Subtype.ext
              dsimp only [positiveAdd, c, b, dn, two]
              omega
            have hright :
                positiveAdd (positiveAdd a dn) ((2 * (k + 1) + 2) * (two : Nat)) = c2 := by
              apply Subtype.ext
              dsimp only [positiveAdd, c2, c, b, dn, two]
              omega
            rwa [hleft, hright]
          have haIH : doublyIndex p a < doublyIndex p (positiveAdd a dn) := by
            have h := ih a ha
            have hdn : (dn : Nat) = 2 * k + 1 := rfl
            rwa [hdn]
          have hresult := haIH.trans hbasePair
          have htarget : positiveAdd (positiveAdd a dn) two =
              positiveAdd a (2 * (k + 1) + 1) := by
            apply Subtype.ext
            dsimp only [positiveAdd, dn, two]
            omega
          rwa [htarget] at hresult
  intro a d ha hd
  obtain ⟨k, hk⟩ := hd
  have h := claim k a ha
  have harg : positiveAdd a (2 * k + 1) = positiveAdd a d := by
    apply Subtype.ext
    dsimp only [positiveAdd]
    omega
  rwa [harg] at h

private theorem exists_least_int_above (Q : Int → Prop) (lo : Int)
    (hex : ∃ z : Int, lo < z ∧ Q z) :
    ∃ z : Int, lo < z ∧ Q z ∧ ∀ w : Int, lo < w → Q w → z ≤ w := by
  classical
  let R : Nat → Prop := fun n => Q (lo + 1 + n)
  have hexR : ∃ n : Nat, R n := by
    obtain ⟨z, hz, hQz⟩ := hex
    let n : Nat := (z - lo - 1).toNat
    have hnonneg : 0 ≤ z - lo - 1 := by omega
    have heq : lo + 1 + (n : Int) = z := by
      dsimp only [n]
      rw [Int.toNat_of_nonneg hnonneg]
      omega
    exact ⟨n, by simpa only [R, heq]⟩
  let n0 : Nat := Nat.find hexR
  refine ⟨lo + 1 + n0, by omega, ?_, ?_⟩
  · exact Nat.find_spec hexR
  · intro w hw hQw
    let n : Nat := (w - lo - 1).toNat
    have hnonneg : 0 ≤ w - lo - 1 := by omega
    have heq : lo + 1 + (n : Int) = w := by
      dsimp only [n]
      rw [Int.toNat_of_nonneg hnonneg]
      omega
    have hRn : R n := by simpa only [R, heq]
    have hmin : n0 ≤ n := Nat.find_min' hexR hRn
    omega

private def reverseDoublyPermutation (p : DoublyInfinitePermutation) :
    DoublyInfinitePermutation :=
  (Equiv.neg Int).trans p

private theorem reverseDoublyPermutation_sequence
    (p : DoublyInfinitePermutation) (z : Int) :
    doublyPermutationSequence (reverseDoublyPermutation p) z =
      doublyPermutationSequence p (-z) := by
  rfl

private theorem reverseDoublyPermutation_index
    (p : DoublyInfinitePermutation) (x : PositiveNat) :
    doublyIndex (reverseDoublyPermutation p) x = -doublyIndex p x := by
  apply (reverseDoublyPermutation p).injective
  change (reverseDoublyPermutation p) ((reverseDoublyPermutation p).symm x) =
    (reverseDoublyPermutation p) (-p.symm x)
  rw [(reverseDoublyPermutation p).apply_symm_apply]
  change x = p (-(-p.symm x))
  rw [neg_neg, p.apply_symm_apply]

private theorem reverseDoublyPermutation_mem_D_three
    (p : DoublyInfinitePermutation) (hp : p ∈ D 3) :
    reverseDoublyPermutation p ∈ D 3 := by
  intro hap
  apply hp
  obtain ⟨pos, hpos, a, d, hd, hvalues⟩ := hap
  let q : Fin 3 → Int := fun i => -pos (Fin.rev i)
  have hq : StrictMono q := by
    intro i j hij
    have hrev : Fin.rev j < Fin.rev i := Fin.rev_lt_rev.mpr hij
    have hposrev := hpos hrev
    dsimp only [q]
    omega
  refine ⟨q, hq, a + 2 * d, -d, ?_, ?_⟩
  · rw [bne_iff_ne] at hd ⊢
    omega
  · intro i
    have hv := hvalues (Fin.rev i)
    change doublyPermutationSequence (reverseDoublyPermutation p) (pos (Fin.rev i)) = _ at hv
    rw [reverseDoublyPermutation_sequence] at hv
    change doublyPermutationSequence p (q i) = _
    rw [hv]
    fin_cases i
    · norm_num
    · norm_num
      ring
    · norm_num

theorem fact_5_holds : fact_5 := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  let one : PositiveNat := ⟨1, by omega⟩
  let two : PositiveNat := ⟨2, by omega⟩
  have h12ne : doublyIndex p one ≠ doublyIndex p two := by
    apply doubly_indices_ne_of_ne p
    intro h
    have hval := congrArg Subtype.val h
    dsimp only [one, two] at hval
    omega
  have contradiction_from_lt : ∀ (p : DoublyInfinitePermutation), p ∈ D 3 →
      doublyIndex p one < doublyIndex p two → False := by
    intro p hp hstart
    have hallEvenRight (x : PositiveNat) (hx : Even (x : Nat)) :
        doublyIndex p one < doublyIndex p x := by
      obtain ⟨r, hr⟩ := even_iff_exists_two_mul.mp hx
      have hrpos : 0 < r := by
        have hxpos := x.property
        omega
      let delta : PositiveNat := ⟨(x : Nat) - 1, by omega⟩
      have hdeltaOdd : Odd (delta : Nat) := by
        refine ⟨r - 1, ?_⟩
        dsimp only [delta]
        omega
      have h := folkman_odd_order_claim_holds p hp
        (by simpa only [one, two] using hstart) one delta
        (by exact ⟨0, rfl⟩) hdeltaOdd
      have htarget : positiveAdd one delta = x := by
        apply Subtype.ext
        dsimp only [positiveAdd, one, delta]
        omega
      rwa [htarget] at h
    have htwoEven : Even (two : Nat) := by
      exact even_iff_exists_two_mul.mpr ⟨1, by rfl⟩
    obtain ⟨z0, hz0right, hz0even, hz0min⟩ :=
      exists_least_int_above
        (fun z : Int => Even ((p z : PositiveNat) : Nat)) (doublyIndex p one)
        ⟨doublyIndex p two, hstart, by
          simpa only [doublyIndex, p.apply_symm_apply] using htwoEven⟩
    let e0 : PositiveNat := p z0
    have hidx0 : doublyIndex p e0 = z0 := by
      simp only [doublyIndex, e0, p.symm_apply_apply]
    have he0even : Even (e0 : Nat) := by exact hz0even
    let e0plus2 : PositiveNat := ⟨(e0 : Nat) + 2, by omega⟩
    have he0plus2Even : Even (e0plus2 : Nat) := by
      obtain ⟨r, hr⟩ := even_iff_exists_two_mul.mp he0even
      apply even_iff_exists_two_mul.mpr
      refine ⟨r + 1, ?_⟩
      dsimp only [e0plus2]
      omega
    have he0plus2Right := hallEvenRight e0plus2 he0plus2Even
    have hz0lePlus : z0 ≤ doublyIndex p e0plus2 := by
      apply hz0min (doublyIndex p e0plus2) he0plus2Right
      simpa only [doublyIndex, p.apply_symm_apply] using he0plus2Even
    have hz0ltPlus : z0 < doublyIndex p e0plus2 := by
      have hne : z0 ≠ doublyIndex p e0plus2 := by
        intro heq
        have hindices : doublyIndex p e0 = doublyIndex p e0plus2 := hidx0.trans heq
        have hvalues := (doubly_indices_ne_of_ne p (x := e0) (y := e0plus2) ?_) hindices
        · exact hvalues.elim
        · intro hxy
          have hval := congrArg Subtype.val hxy
          dsimp only [e0plus2] at hval
          omega
      omega
    obtain ⟨z1, hz1right, hz1prop, hz1min⟩ :=
      exists_least_int_above
        (fun z : Int => Even ((p z : PositiveNat) : Nat) ∧
          (e0 : Nat) < (p z : Nat)) z0
        ⟨doublyIndex p e0plus2, hz0ltPlus, by
          constructor
          · simpa only [doublyIndex, p.apply_symm_apply] using he0plus2Even
          · simp only [doublyIndex, p.apply_symm_apply, e0plus2]
            omega⟩
    let e1 : PositiveNat := p z1
    have hidx1 : doublyIndex p e1 = z1 := by
      simp only [doublyIndex, e1, p.symm_apply_apply]
    have he1even : Even (e1 : Nat) := hz1prop.1
    have he01 : (e0 : Nat) < (e1 : Nat) := hz1prop.2
    obtain ⟨r, hr⟩ := even_iff_exists_two_mul.mp he0even
    obtain ⟨s, hs⟩ := even_iff_exists_two_mul.mp he1even
    let delta : Nat := s - r
    have hdelta : 0 < delta := by
      dsimp only [delta]
      omega
    let e2 : PositiveNat := ⟨(e0 : Nat) + 4 * delta, by omega⟩
    have he2even : Even (e2 : Nat) := by
      apply even_iff_exists_two_mul.mpr
      refine ⟨r + 2 * delta, ?_⟩
      dsimp only [e2]
      omega
    have he2right := hallEvenRight e2 he2even
    have hz0le2 : z0 ≤ doublyIndex p e2 := by
      apply hz0min (doublyIndex p e2) he2right
      simpa only [doublyIndex, p.apply_symm_apply] using he2even
    have hz0lt2 : z0 < doublyIndex p e2 := by
      have hne : z0 ≠ doublyIndex p e2 := by
        intro heq
        have hindices : doublyIndex p e0 = doublyIndex p e2 := hidx0.trans heq
        apply (doubly_indices_ne_of_ne p (x := e0) (y := e2) ?_) hindices
        intro hxy
        have hval := congrArg Subtype.val hxy
        dsimp only [e2] at hval
        omega
      omega
    have hz1le2 : z1 ≤ doublyIndex p e2 := by
      apply hz1min (doublyIndex p e2) hz0lt2
      constructor
      · simpa only [doublyIndex, p.apply_symm_apply] using he2even
      · simp only [doublyIndex, p.apply_symm_apply]
        dsimp only [e2, delta]
        omega
    have hz1lt2 : z1 < doublyIndex p e2 := by
      have hne : z1 ≠ doublyIndex p e2 := by
        intro heq
        have hindices : doublyIndex p e1 = doublyIndex p e2 := hidx1.trans heq
        apply (doubly_indices_ne_of_ne p (x := e1) (y := e2) ?_) hindices
        intro hxy
        have hval := congrArg Subtype.val hxy
        dsimp only [e2, delta] at hval
        omega
      omega
    apply hp
    let pos : Fin 3 → Int :=
      Fin.cases z0 (Fin.cases z1 (Fin.cases (doublyIndex p e2) Fin.elim0))
    have hpos0 : pos 0 = z0 := rfl
    have hpos1 : pos 1 = z1 := rfl
    have hpos2 : pos 2 = doublyIndex p e2 := rfl
    refine ⟨pos, ?_, (e0 : Nat), (2 * delta : Nat), ?_, ?_⟩
    · rw [Fin.strictMono_iff_lt_succ]
      intro i
      fin_cases i
      · change pos 0 < pos 1
        rw [hpos0, hpos1]
        exact hz1right
      · change pos 1 < pos 2
        rw [hpos1, hpos2]
        exact hz1lt2
    · rw [bne_iff_ne]
      exact_mod_cast (by omega : 2 * delta ≠ 0)
    · intro i
      fin_cases i
      · change doublyPermutationSequence p (pos 0) = _
        rw [hpos0]
        change ((p z0 : Nat) : Int) = _
        dsimp only [e0]
        simp
      · change doublyPermutationSequence p (pos 1) = _
        rw [hpos1]
        change (((e1 : PositiveNat) : Nat) : Int) = _
        push_cast
        dsimp only [delta]
        omega
      · change doublyPermutationSequence p (pos 2) = _
        rw [hpos2, doubly_value_at_index]
        dsimp only [e2]
        push_cast
        ring
  rcases lt_or_gt_of_ne h12ne with hlt | hgt
  · exact contradiction_from_lt p hp hlt
  · let q : DoublyInfinitePermutation := reverseDoublyPermutation p
    have hq : q ∈ D 3 := reverseDoublyPermutation_mem_D_three p hp
    have hqstart : doublyIndex q one < doublyIndex q two := by
      dsimp only [q]
      rw [reverseDoublyPermutation_index, reverseDoublyPermutation_index]
      omega
    exact contradiction_from_lt q hq hqstart

private theorem concludingIntervalLength_pos :
    ∀ k : Nat, 0 < concludingIntervalLength k := by
  intro k
  induction k with
  | zero => simp [concludingIntervalLength]
  | succ k ih =>
      rw [concludingIntervalLength]
      exact Nat.div_pos (by omega) (by omega)

private theorem concludingIntervalStart_succ (k : Nat) :
    concludingIntervalStart (k + 1) =
      concludingIntervalStart k + concludingIntervalLength k := by
  simp only [concludingIntervalStart, sum_range_succ]
  ac_rfl

private theorem concludingIntervalStart_strictMono :
    StrictMono concludingIntervalStart := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [concludingIntervalStart_succ]
  exact Nat.lt_add_of_pos_right (concludingIntervalLength_pos k)

private theorem concludingIntervalStart_lower :
    ∀ k : Nat, k + 1 ≤ concludingIntervalStart k := by
  intro k
  induction k with
  | zero => simp [concludingIntervalStart]
  | succ k ih =>
      rw [concludingIntervalStart_succ]
      have hlen := concludingIntervalLength_pos k
      omega

private theorem concludingInterval_mem_iff (x k : Nat) :
    x ∈ concludingInterval k ↔
      concludingIntervalStart k ≤ x ∧ x < concludingIntervalStart (k + 1) := by
  rw [concludingIntervalStart_succ]
  simp only [concludingInterval, mem_Icc]
  have hlen := concludingIntervalLength_pos k
  omega

theorem concluding_intervals_partition_holds : concluding_intervals_partition := by
  constructor
  · simp [concludingInterval, concludingIntervalStart, concludingIntervalLength]
  constructor
  · intro k
    rfl
  · intro x
    let P : Nat → Prop := fun k => (x : Nat) < concludingIntervalStart (k + 1)
    have hexists : ∃ k : Nat, P k := by
      refine ⟨(x : Nat), ?_⟩
      dsimp only [P]
      have hbound := concludingIntervalStart_lower ((x : Nat) + 1)
      omega
    let k : Nat := Nat.find hexists
    have hupper : (x : Nat) < concludingIntervalStart (k + 1) := by
      exact Nat.find_spec hexists
    have hlower : concludingIntervalStart k ≤ (x : Nat) := by
      by_cases hk : k = 0
      · rw [hk]
        simp only [concludingIntervalStart, sum_range_zero, add_zero]
        omega
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have hnot := Nat.find_min hexists (show k - 1 < k by omega)
        have hpred : k - 1 + 1 = k := by omega
        dsimp only [P] at hnot
        rw [hpred] at hnot
        omega
    refine ⟨k, (concludingInterval_mem_iff (x : Nat) k).mpr ⟨hlower, hupper⟩, ?_⟩
    intro l hl
    have hlbounds := (concludingInterval_mem_iff (x : Nat) l).mp hl
    apply le_antisymm
    · by_contra hnot
      have hkl : k < l := by omega
      have hstarts := concludingIntervalStart_strictMono.monotone
        (show k + 1 ≤ l by omega)
      exact (not_lt_of_ge hstarts) (lt_of_le_of_lt hlbounds.1 hupper)
    · by_contra hnot
      have hlk : l < k := by omega
      have hstarts := concludingIntervalStart_strictMono.monotone
        (show l + 1 ≤ k by omega)
      exact (not_lt_of_ge hstarts) (lt_of_le_of_lt hlower hlbounds.2)

end LeanProofs.DavisEntringerGrahamSimmons1977
