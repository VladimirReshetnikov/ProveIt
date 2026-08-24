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
  simp only [Fin.isValue, Nat.cast_zero, zero_mul, add_zero] at h0
  norm_num at h1 h2
  refine ⟨x 0, x 1 - x 0, ?_, ?_⟩
  · rw [bne_iff_ne] at hd ⊢
    intro heq
    have : x 1 = x 0 := sub_eq_zero.mp heq
    omega
  · intro i
    fin_cases i <;> simp <;> omega

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

end LeanProofs.DavisEntringerGrahamSimmons1977
