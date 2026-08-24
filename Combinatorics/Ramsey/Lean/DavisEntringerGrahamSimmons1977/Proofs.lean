import DavisEntringerGrahamSimmons1977.Statements
import Mathlib.Data.List.NodupEquivFin

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

end LeanProofs.DavisEntringerGrahamSimmons1977
