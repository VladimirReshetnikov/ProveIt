import DavisEntringerGrahamSimmons1977.Proofs
import Mathlib

/-!
# Counting recurrences for Davis--Entringer--Graham--Simmons (1977)

This module turns the paper's parity block construction into an injective map
on finite progression-free permutations, proving its even counting recurrence.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace LeanProofs.DavisEntringerGrahamSimmons1977

private def permutationWord {n : Nat} (p : FinitePermutation n) : Block :=
  List.ofFn (fun i => (p i : Nat) + 1)

private theorem permutationWord_length {n : Nat} (p : FinitePermutation n) :
    (permutationWord p).length = n := by
  simp [permutationWord]

private theorem permutationWord_getElem {n i : Nat} (p : FinitePermutation n)
    (hi : i < n) :
    (permutationWord p)[i]'(by simpa [permutationWord] using hi) =
      (p ⟨i, hi⟩ : Nat) + 1 := by
  simp [permutationWord]

private theorem permutationWord_free {n : Nat} (p : FinitePermutation n)
    (hp : FiniteAPFree p 3) : BlockAPFree (permutationWord p) 3 := by
  intro hap
  apply hp
  obtain ⟨pos, hpos, hprog⟩ := hap
  refine ⟨fun i => ⟨pos i, by simpa [permutationWord] using (pos i).isLt⟩, ?_, ?_⟩
  · intro i j hij
    exact hpos hij
  · simpa [blockSequence, permutationWord, finitePermutationSequence] using hprog

private theorem permutationWord_positive {n : Nat} (p : FinitePermutation n) :
    ∀ x : Nat, x ∈ permutationWord p → 0 < x := by
  intro x hx
  simp only [permutationWord, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  omega

private def parityPermutationFun (n : Nat) (oddFirst : Bool)
    (p q : FinitePermutation n) (i : Fin (2 * n)) : Fin (2 * n) :=
  if hi : (i : Nat) < n then
    if oddFirst then
      ⟨2 * (q ⟨i, hi⟩ : Nat), by have := (q ⟨i, hi⟩).isLt; omega⟩
    else
      ⟨2 * (p ⟨i, hi⟩ : Nat) + 1, by have := (p ⟨i, hi⟩).isLt; omega⟩
  else
    let j : Fin n := ⟨(i : Nat) - n, by omega⟩
    if oddFirst then
      ⟨2 * (p j : Nat) + 1, by have := (p j).isLt; omega⟩
    else
      ⟨2 * (q j : Nat), by have := (q j).isLt; omega⟩

private theorem parityPermutationFun_injective (n : Nat) (oddFirst : Bool)
    (p q : FinitePermutation n) :
    Function.Injective (parityPermutationFun n oddFirst p q) := by
  intro i j hij
  have hijv := congrArg Fin.val hij
  by_cases hi : (i : Nat) < n <;> by_cases hj : (j : Nat) < n
  · simp only [parityPermutationFun, dif_pos hi, dif_pos hj] at hij
    simp only [parityPermutationFun, dif_pos hi, dif_pos hj] at hijv
    cases oddFirst
    · simp only [Bool.false_eq_true, ↓reduceIte] at hijv
      have hp : p ⟨i, hi⟩ = p ⟨j, hj⟩ := by
        apply Fin.ext
        apply Nat.mul_left_cancel (by omega : 0 < 2)
        omega
      have hinner := p.injective hp
      have hval : (i : Nat) = (j : Nat) :=
        congrArg (fun z : Fin n => z.val) hinner
      exact Fin.ext hval
    · simp only [↓reduceIte] at hijv
      have hq : q ⟨i, hi⟩ = q ⟨j, hj⟩ := by
        apply Fin.ext
        exact Nat.mul_left_cancel (by omega) hijv
      have hinner := q.injective hq
      have hval : (i : Nat) = (j : Nat) :=
        congrArg (fun z : Fin n => z.val) hinner
      exact Fin.ext hval
  · simp only [parityPermutationFun, dif_pos hi, dif_neg hj] at hijv
    cases oddFirst <;> simp only [Bool.false_eq_true, ↓reduceIte] at hijv <;> omega
  · simp only [parityPermutationFun, dif_neg hi, dif_pos hj] at hijv
    cases oddFirst <;> simp only [Bool.false_eq_true, ↓reduceIte] at hijv <;> omega
  · simp only [parityPermutationFun, dif_neg hi, dif_neg hj] at hijv
    cases oddFirst
    · simp only [Bool.false_eq_true, ↓reduceIte] at hijv
      have hq : q ⟨(i : Nat) - n, by omega⟩ = q ⟨(j : Nat) - n, by omega⟩ := by
        apply Fin.ext
        exact Nat.mul_left_cancel (by omega) hijv
      have hinner := q.injective hq
      have hsub : (i : Nat) - n = (j : Nat) - n :=
        congrArg (fun z : Fin n => z.val) hinner
      apply Fin.ext
      omega
    · simp only [↓reduceIte] at hijv
      have hp : p ⟨(i : Nat) - n, by omega⟩ = p ⟨(j : Nat) - n, by omega⟩ := by
        apply Fin.ext
        omega
      have hinner := p.injective hp
      have hsub : (i : Nat) - n = (j : Nat) - n :=
        congrArg (fun z : Fin n => z.val) hinner
      apply Fin.ext
      omega

private def parityPermutation (n : Nat) (oddFirst : Bool)
    (p q : FinitePermutation n) : FinitePermutation (2 * n) :=
  Equiv.ofBijective (parityPermutationFun n oddFirst p q)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨parityPermutationFun_injective n oddFirst p q, rfl⟩)

private theorem parityPermutation_apply (n : Nat) (oddFirst : Bool)
    (p q : FinitePermutation n) (i : Fin (2 * n)) :
    parityPermutation n oddFirst p q i = parityPermutationFun n oddFirst p q i := by
  rfl

private def parityBlock {n : Nat} (oddFirst : Bool)
    (p q : FinitePermutation n) : Block :=
  if oddFirst then parityLiftOddFirst (permutationWord p) (permutationWord q)
  else parityLift (permutationWord p) (permutationWord q)

private theorem parityBlock_length {n : Nat} (oddFirst : Bool)
    (p q : FinitePermutation n) :
    (parityBlock oddFirst p q).length = 2 * n := by
  cases oddFirst <;>
    simp [parityBlock, parityLift, parityLiftOddFirst, twiceBlock,
      permutationWord, Nat.two_mul]

private theorem parityPermutation_sequence_eq {n : Nat} (oddFirst : Bool)
    (p q : FinitePermutation n) (i : Fin (2 * n)) :
    finitePermutationSequence (parityPermutation n oddFirst p q) i =
      blockSequence (parityBlock oddFirst p q)
        ⟨i, by rw [parityBlock_length]; exact i.isLt⟩ := by
  by_cases hi : (i : Nat) < n
  · cases oddFirst <;>
      simp [finitePermutationSequence, parityPermutation_apply,
        parityPermutationFun, hi, parityBlock, parityLift,
        parityLiftOddFirst, twiceBlock, permutationWord, blockSequence,
        List.get_eq_getElem, Nat.two_mul] <;> omega
  · cases oddFirst
    · simp only [finitePermutationSequence, parityPermutation_apply,
        parityPermutationFun, dif_neg hi, Bool.false_eq_true, ↓reduceIte,
        parityBlock, parityLift, twiceBlock, permutationWord, blockSequence,
        List.get_eq_getElem]
      rw [List.getElem_append_right (by simp; omega)]
      simp
      omega
    · simp only [finitePermutationSequence, parityPermutation_apply,
        parityPermutationFun, dif_neg hi, ↓reduceIte, parityBlock,
        parityLiftOddFirst, twiceBlock, permutationWord, blockSequence,
        List.get_eq_getElem]
      rw [List.getElem_append_right (by simp; omega)]
      simp
      omega

private theorem parityPermutation_free {n : Nat} (oddFirst : Bool)
    (p q : FinitePermutation n) (hp : FiniteAPFree p 3)
    (hq : FiniteAPFree q 3) :
    FiniteAPFree (parityPermutation n oddFirst p q) 3 := by
  have hblocks := parity_construction_is_ap_free_holds
    (permutationWord p) (permutationWord q)
    (permutationWord_positive p) (permutationWord_positive q)
    (permutationWord_free p hp) (permutationWord_free q hq)
  have hblock : BlockAPFree (parityBlock oddFirst p q) 3 := by
    cases oddFirst
    · exact hblocks.1
    · exact hblocks.2
  intro hap
  apply hblock
  obtain ⟨pos, hpos, hprogression⟩ := hap
  let blockPos : Fin 3 → Fin (parityBlock oddFirst p q).length := fun i =>
    ⟨pos i, by rw [parityBlock_length]; exact (pos i).isLt⟩
  refine ⟨blockPos, ?_, ?_⟩
  · intro i j hij
    exact hpos hij
  · convert hprogression using 1
    funext i
    exact (parityPermutation_sequence_eq oddFirst p q (pos i)).symm

private abbrev FreePermutation (n : Nat) :=
  {p : FinitePermutation n // FiniteAPFree p 3}

private def evenParityEmbedding (n : Nat) :
    Bool × (FreePermutation n × FreePermutation n) → FreePermutation (2 * n) :=
  fun ⟨b, ⟨p, hp⟩, ⟨q, hq⟩⟩ =>
    ⟨parityPermutation n b p q, parityPermutation_free b p q hp hq⟩

private theorem evenParityEmbedding_injective (n : Nat) (hn : 0 < n) :
    Function.Injective (evenParityEmbedding n) := by
  rintro ⟨b, p, q⟩ ⟨b', p', q'⟩ heq
  have hperm : parityPermutation n b p q = parityPermutation n b' p' q' :=
    congrArg Subtype.val heq
  have hb : b = b' := by
    cases b <;> cases b'
    · rfl
    · have hvalue := congrArg
          (fun e : FinitePermutation (2 * n) =>
            (e ⟨0, by omega⟩ : Nat)) hperm
      simp [parityPermutation_apply, parityPermutationFun, hn] at hvalue
      omega
    · have hvalue := congrArg
          (fun e : FinitePermutation (2 * n) =>
            (e ⟨0, by omega⟩ : Nat)) hperm
      simp [parityPermutation_apply, parityPermutationFun, hn] at hvalue
      omega
    · rfl
  subst b'
  have hp : (p : FinitePermutation n) = p' := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    cases b
    · have hvalue := congrArg
          (fun e : FinitePermutation (2 * n) =>
            (e ⟨i, by omega⟩ : Nat)) hperm
      simp [parityPermutation_apply, parityPermutationFun] at hvalue
      omega
    · have hvalue := congrArg
          (fun e : FinitePermutation (2 * n) =>
            (e ⟨n + i, by omega⟩ : Nat)) hperm
      simp [parityPermutation_apply, parityPermutationFun] at hvalue
      omega
  have hq : (q : FinitePermutation n) = q' := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    cases b
    · have hvalue := congrArg
          (fun e : FinitePermutation (2 * n) =>
            (e ⟨n + i, by omega⟩ : Nat)) hperm
      simp [parityPermutation_apply, parityPermutationFun] at hvalue
      omega
    · have hvalue := congrArg
          (fun e : FinitePermutation (2 * n) =>
            (e ⟨i, by omega⟩ : Nat)) hperm
      simp [parityPermutation_apply, parityPermutationFun, i.isLt] at hvalue
      omega
  have hp' : p = p' := Subtype.ext hp
  have hq' : q = q' := Subtype.ext hq
  subst p'
  subst q'
  rfl

theorem even_count_recurrence_holds : even_count_recurrence := by
  classical
  intro n hn
  have hcard := Fintype.card_le_of_injective (evenParityEmbedding n)
    (evenParityEmbedding_injective n hn)
  change 2 * M n ^ 2 ≤ M (2 * n)
  simpa [M, Fintype.card_prod, pow_two, Nat.mul_assoc] using hcard


private def oddParityPermutationFun (n : Nat) (oddFirst : Bool)
    (p : FinitePermutation n) (q : FinitePermutation (n + 1))
    (i : Fin (2 * n + 1)) : Fin (2 * n + 1) :=
  if oddFirst then
    if hi : (i : Nat) < n + 1 then
      ⟨2 * (q ⟨i, hi⟩ : Nat), by have := (q ⟨i, hi⟩).isLt; omega⟩
    else
      let j : Fin n := ⟨(i : Nat) - (n + 1), by omega⟩
      ⟨2 * (p j : Nat) + 1, by have := (p j).isLt; omega⟩
  else
    if hi : (i : Nat) < n then
      ⟨2 * (p ⟨i, hi⟩ : Nat) + 1, by have := (p ⟨i, hi⟩).isLt; omega⟩
    else
      let j : Fin (n + 1) := ⟨(i : Nat) - n, by omega⟩
      ⟨2 * (q j : Nat), by have := (q j).isLt; omega⟩

private theorem oddParityPermutationFun_injective (n : Nat) (oddFirst : Bool)
    (p : FinitePermutation n) (q : FinitePermutation (n + 1)) :
    Function.Injective (oddParityPermutationFun n oddFirst p q) := by
  intro i j hij
  have hijv := congrArg Fin.val hij
  cases oddFirst
  · simp only [oddParityPermutationFun, Bool.false_eq_true, ↓reduceIte] at hijv
    by_cases hi : (i : Nat) < n <;> by_cases hj : (j : Nat) < n
    · simp only [dif_pos hi, dif_pos hj] at hijv
      have hp : p ⟨i, hi⟩ = p ⟨j, hj⟩ := by
        apply Fin.ext
        omega
      have hinner := p.injective hp
      have hval : (i : Nat) = (j : Nat) :=
        congrArg (fun z : Fin n => z.val) hinner
      exact Fin.ext hval
    · simp only [dif_pos hi, dif_neg hj] at hijv
      omega
    · simp only [dif_neg hi, dif_pos hj] at hijv
      omega
    · simp only [dif_neg hi, dif_neg hj] at hijv
      have hq : q ⟨(i : Nat) - n, by omega⟩ =
          q ⟨(j : Nat) - n, by omega⟩ := by
        apply Fin.ext
        exact Nat.mul_left_cancel (by omega) hijv
      have hinner := q.injective hq
      have hsub : (i : Nat) - n = (j : Nat) - n :=
        congrArg (fun z : Fin (n + 1) => z.val) hinner
      apply Fin.ext
      omega
  · simp only [oddParityPermutationFun, ↓reduceIte] at hijv
    by_cases hi : (i : Nat) < n + 1 <;> by_cases hj : (j : Nat) < n + 1
    · simp only [dif_pos hi, dif_pos hj] at hijv
      have hq : q ⟨i, hi⟩ = q ⟨j, hj⟩ := by
        apply Fin.ext
        exact Nat.mul_left_cancel (by omega) hijv
      have hinner := q.injective hq
      have hval : (i : Nat) = (j : Nat) :=
        congrArg (fun z : Fin (n + 1) => z.val) hinner
      exact Fin.ext hval
    · simp only [dif_pos hi, dif_neg hj] at hijv
      omega
    · simp only [dif_neg hi, dif_pos hj] at hijv
      omega
    · simp only [dif_neg hi, dif_neg hj] at hijv
      have hp : p ⟨(i : Nat) - (n + 1), by omega⟩ =
          p ⟨(j : Nat) - (n + 1), by omega⟩ := by
        apply Fin.ext
        omega
      have hinner := p.injective hp
      have hsub : (i : Nat) - (n + 1) = (j : Nat) - (n + 1) :=
        congrArg (fun z : Fin n => z.val) hinner
      apply Fin.ext
      omega

private def oddParityPermutation (n : Nat) (oddFirst : Bool)
    (p : FinitePermutation n) (q : FinitePermutation (n + 1)) :
    FinitePermutation (2 * n + 1) :=
  Equiv.ofBijective (oddParityPermutationFun n oddFirst p q)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨oddParityPermutationFun_injective n oddFirst p q, rfl⟩)

private theorem oddParityPermutation_apply (n : Nat) (oddFirst : Bool)
    (p : FinitePermutation n) (q : FinitePermutation (n + 1))
    (i : Fin (2 * n + 1)) :
    oddParityPermutation n oddFirst p q i =
      oddParityPermutationFun n oddFirst p q i := by
  rfl

private def oddParityBlock {n : Nat} (oddFirst : Bool)
    (p : FinitePermutation n) (q : FinitePermutation (n + 1)) : Block :=
  if oddFirst then parityLiftOddFirst (permutationWord p) (permutationWord q)
  else parityLift (permutationWord p) (permutationWord q)

private theorem oddParityBlock_length {n : Nat} (oddFirst : Bool)
    (p : FinitePermutation n) (q : FinitePermutation (n + 1)) :
    (oddParityBlock oddFirst p q).length = 2 * n + 1 := by
  cases oddFirst
  · simp [oddParityBlock, parityLift, twiceBlock,
      permutationWord, Nat.two_mul]
    omega
  · simp [oddParityBlock, parityLiftOddFirst, twiceBlock,
      permutationWord, Nat.two_mul]

private theorem oddParityPermutation_sequence_eq {n : Nat} (oddFirst : Bool)
    (p : FinitePermutation n) (q : FinitePermutation (n + 1))
    (i : Fin (2 * n + 1)) :
    finitePermutationSequence (oddParityPermutation n oddFirst p q) i =
      blockSequence (oddParityBlock oddFirst p q)
        ⟨i, by rw [oddParityBlock_length]; exact i.isLt⟩ := by
  cases oddFirst
  · by_cases hi : (i : Nat) < n
    · simp [oddParityPermutation_apply, oddParityPermutationFun, hi,
        finitePermutationSequence, oddParityBlock, parityLift,
        twiceBlock, permutationWord, blockSequence, List.get_eq_getElem]
      omega
    · simp only [oddParityPermutation_apply, oddParityPermutationFun,
        Bool.false_eq_true, ↓reduceIte, dif_neg hi, finitePermutationSequence,
        oddParityBlock, parityLift, blockSequence, List.get_eq_getElem]
      rw [List.getElem_append_right (by
        simp [twiceBlock, permutationWord]
        omega)]
      rw [List.getElem_map]
      simp only [twiceBlock, List.length_map, permutationWord_length]
      rw [permutationWord_getElem q (by omega)]
      omega
  · by_cases hi : (i : Nat) < n + 1
    · simp only [oddParityPermutation_apply, oddParityPermutationFun,
        ↓reduceIte, dif_pos hi, finitePermutationSequence, oddParityBlock,
        parityLiftOddFirst, blockSequence, List.get_eq_getElem]
      rw [List.getElem_append_left (by simp [permutationWord]; omega)]
      rw [List.getElem_map, permutationWord_getElem q hi]
      omega
    · simp only [oddParityPermutation_apply, oddParityPermutationFun,
        ↓reduceIte, dif_neg hi, finitePermutationSequence, oddParityBlock,
        parityLiftOddFirst, twiceBlock, permutationWord,
        blockSequence, List.get_eq_getElem]
      rw [List.getElem_append_right (by simp; omega)]
      simp
      omega

private theorem oddParityPermutation_free {n : Nat} (oddFirst : Bool)
    (p : FinitePermutation n) (q : FinitePermutation (n + 1))
    (hp : FiniteAPFree p 3) (hq : FiniteAPFree q 3) :
    FiniteAPFree (oddParityPermutation n oddFirst p q) 3 := by
  have hblocks := parity_construction_is_ap_free_holds
    (permutationWord p) (permutationWord q)
    (permutationWord_positive p) (permutationWord_positive q)
    (permutationWord_free p hp) (permutationWord_free q hq)
  have hblock : BlockAPFree (oddParityBlock oddFirst p q) 3 := by
    cases oddFirst
    · exact hblocks.1
    · exact hblocks.2
  intro hap
  apply hblock
  obtain ⟨pos, hpos, hprogression⟩ := hap
  let blockPos : Fin 3 → Fin (oddParityBlock oddFirst p q).length := fun i =>
    ⟨pos i, by rw [oddParityBlock_length]; exact (pos i).isLt⟩
  refine ⟨blockPos, ?_, ?_⟩
  · intro i j hij
    exact hpos hij
  · convert hprogression using 1
    funext i
    exact (oddParityPermutation_sequence_eq oddFirst p q (pos i)).symm

private def oddParityEmbedding (n : Nat) :
    Bool × (FreePermutation n × FreePermutation (n + 1)) →
      FreePermutation (2 * n + 1) :=
  fun ⟨b, ⟨p, hp⟩, ⟨q, hq⟩⟩ =>
    ⟨oddParityPermutation n b p q, oddParityPermutation_free b p q hp hq⟩

private theorem oddParityEmbedding_injective (n : Nat) (hn : 0 < n) :
    Function.Injective (oddParityEmbedding n) := by
  rintro ⟨b, p, q⟩ ⟨b', p', q'⟩ heq
  have hperm : oddParityPermutation n b p q = oddParityPermutation n b' p' q' :=
    congrArg Subtype.val heq
  have hb : b = b' := by
    cases b <;> cases b'
    · rfl
    · have hvalue := congrArg
          (fun e : FinitePermutation (2 * n + 1) =>
            (e ⟨0, by omega⟩ : Nat)) hperm
      simp [oddParityPermutation_apply, oddParityPermutationFun, hn] at hvalue
      omega
    · have hvalue := congrArg
          (fun e : FinitePermutation (2 * n + 1) =>
            (e ⟨0, by omega⟩ : Nat)) hperm
      simp [oddParityPermutation_apply, oddParityPermutationFun, hn] at hvalue
      omega
    · rfl
  subst b'
  have hp : (p : FinitePermutation n) = p' := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    cases b
    · have hvalue := congrArg
          (fun e : FinitePermutation (2 * n + 1) =>
            (e ⟨i, by omega⟩ : Nat)) hperm
      simp [oddParityPermutation_apply, oddParityPermutationFun, i.isLt] at hvalue
      omega
    · have hvalue := congrArg
          (fun e : FinitePermutation (2 * n + 1) =>
            (e ⟨n + 1 + i, by omega⟩ : Nat)) hperm
      have hnot : ¬n + 1 + (i : Nat) < n + 1 := by omega
      simp [oddParityPermutation_apply, oddParityPermutationFun, hnot] at hvalue
      omega
  have hq : (q : FinitePermutation (n + 1)) = q' := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    cases b
    · have hvalue := congrArg
          (fun e : FinitePermutation (2 * n + 1) =>
            (e ⟨n + i, by omega⟩ : Nat)) hperm
      simp [oddParityPermutation_apply, oddParityPermutationFun] at hvalue
      omega
    · have hvalue := congrArg
          (fun e : FinitePermutation (2 * n + 1) =>
            (e ⟨i, by omega⟩ : Nat)) hperm
      simp [oddParityPermutation_apply, oddParityPermutationFun, i.isLt] at hvalue
      omega
  have hp' : p = p' := Subtype.ext hp
  have hq' : q = q' := Subtype.ext hq
  subst p'
  subst q'
  rfl

theorem odd_count_recurrence_holds : odd_count_recurrence := by
  classical
  intro n hn
  have hcard := Fintype.card_le_of_injective (oddParityEmbedding n)
    (oddParityEmbedding_injective n hn)
  simp only [Fintype.card_prod, Fintype.card_bool] at hcard
  change 2 * Fintype.card (FreePermutation (n + 1)) *
      Fintype.card (FreePermutation n) ≤
    Fintype.card (FreePermutation (2 * n + 1))
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcard

private theorem M_pos (n : Nat) (hn : 0 < n) : 0 < M n := by
  classical
  obtain ⟨p, hp⟩ := finite_ap_free_permutation_exists_holds n hn
  unfold M
  rw [Fintype.card_pos_iff]
  exact ⟨⟨p, hp⟩⟩

theorem fact_1_holds : fact_1 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
      · subst n
        have hkpos : 0 < k := by omega
        have hkind : k < 2 * k := by omega
        have hlower := ih k hkind (by omega : 1 ≤ k)
        have hrec := even_count_recurrence_holds k hkpos
        have hexp : 2 ^ (2 * k - 1) = 2 * (2 ^ (k - 1)) ^ 2 := by
          rw [show 2 * k - 1 = (k - 1) + (k - 1) + 1 by omega]
          simp only [pow_add, pow_one]
          ring
        rw [hexp]
        calc
          2 * (2 ^ (k - 1)) ^ 2 ≤ 2 * M k ^ 2 := by gcongr
          _ ≤ M (2 * k) := hrec
      · subst n
        by_cases hkzero : k = 0
        · subst k
          norm_num
          exact M_pos 1 Nat.one_pos
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
          have hkind : k < 2 * k + 1 := by omega
          have hksuccind : k + 1 < 2 * k + 1 := by omega
          have hlower := ih k hkind (by omega : 1 ≤ k)
          have hlowerSucc := ih (k + 1) hksuccind (by omega : 1 ≤ k + 1)
          have hlowerSucc' : 2 ^ k ≤ M (k + 1) := by
            simpa using hlowerSucc
          have hrec := odd_count_recurrence_holds k hkpos
          have hexp : 2 ^ (2 * k) = 2 * 2 ^ k * 2 ^ (k - 1) := by
            rw [show 2 * k = k + (k - 1) + 1 by omega]
            simp only [pow_add, pow_one]
            ring
          rw [show 2 * k + 1 - 1 = 2 * k by omega, hexp]
          calc
            2 * 2 ^ k * 2 ^ (k - 1) ≤ 2 * M (k + 1) * M k := by
              gcongr
            _ ≤ M (2 * k + 1) := hrec

end LeanProofs.DavisEntringerGrahamSimmons1977
