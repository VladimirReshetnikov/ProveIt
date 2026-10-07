import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Sort

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem binary_eq_zero_of_ne_one (b : Fin 2) (h : b ≠ 1) : b = 0 := by
  apply Fin.ext
  have hb := b.isLt
  have hn : b.val ≠ 1 := fun heq => h (Fin.ext heq)
  change b.val = 0
  omega

theorem binary_eq_one_of_ne_zero (b : Fin 2) (h : b ≠ 0) : b = 1 := by
  apply Fin.ext
  have hb := b.isLt
  have hn : b.val ≠ 0 := fun heq => h (Fin.ext heq)
  change b.val = 1
  omega

def binaryZeroCount {n : ℕ} (f : Fin n → Fin 2) : ℕ :=
  Fintype.card {i : Fin n // f i = 0}

def binarySorted {n : ℕ} (f : Fin n → Fin 2) : Fin n → Fin 2 := f ∘ Tuple.sort f

theorem binaryZeroCount_comp {n : ℕ} (f : Fin n → Fin 2) (e : Equiv.Perm (Fin n)) :
    binaryZeroCount (f ∘ e) = binaryZeroCount f := by
  exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

theorem binarySorted_comp {n : ℕ} (f : Fin n → Fin 2) (e : Equiv.Perm (Fin n)) :
    binarySorted (f ∘ e) = binarySorted f :=
  Tuple.comp_perm_comp_sort_eq_comp_sort

theorem binarySorted_threshold {n : ℕ} (f : Fin n → Fin 2) (k : Fin n) :
    binarySorted f k = if k.val < binaryZeroCount f then 0 else 1 := by
  have hle (a : Fin 2) : a ≤ 0 ↔ a = 0 :=
    ⟨fun h => le_antisymm h (Fin.zero_le _), fun h => h ▸ le_rfl⟩
  have hiff : k.val < binaryZeroCount (binarySorted f) ↔ binarySorted f k = 0 := by
    have H := Tuple.lt_card_le_iff_apply_le_of_monotone
      (f := binarySorted f) (j := k) (a := (0 : Fin 2)) (Tuple.monotone_sort f)
    unfold binaryZeroCount
    rw [Fintype.card_subtype]
    have hfilter : (Finset.univ.filter (fun i : Fin n => binarySorted f i = 0)) =
        Finset.univ.filter (fun i : Fin n => binarySorted f i ≤ 0) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hle]
    rw [hfilter]
    exact H.trans (hle _)
  have hcount : binaryZeroCount (binarySorted f) = binaryZeroCount f :=
    binaryZeroCount_comp f (Tuple.sort f)
  rw [hcount] at hiff
  split_ifs with hk
  · exact hiff.mp hk
  · exact binary_eq_one_of_ne_zero _ (fun h => hk (hiff.mpr h))

def zeroFixedPermutation {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.cases 0 (fun j => (e j).succ)
  invFun := Fin.cases 0 (fun j => (e.symm j).succ)
  left_inv j := by
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · simp only [Fin.cases_succ, Equiv.symm_apply_apply]
  right_inv j := by
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · simp only [Fin.cases_succ, Equiv.apply_symm_apply]

theorem binarySorted_tail {n : ℕ} (f : Fin (n + 1) → Fin 2) (h0 : f 0 = 0) :
    binarySorted f = f ∘ zeroFixedPermutation (Tuple.sort (fun j => f j.succ)) := by
  have hm : Monotone (f ∘ zeroFixedPermutation (Tuple.sort (fun j => f j.succ))) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j _
      change f 0 ≤ _
      rw [h0]
      exact Fin.zero_le _
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        have hi : ¬ i.succ ≤ (0 : Fin (n + 1)) := by
          intro h
          simp only [Fin.le_def, Fin.val_succ, Fin.val_zero] at h
          omega
        exact (hi hij).elim
      · intro hij
        exact (Tuple.monotone_sort (fun j : Fin n => f j.succ))
          (by simpa only [Fin.succ_le_succ_iff] using hij)
  exact Tuple.unique_monotone (Tuple.monotone_sort f) hm

end Erdos3

end

end OAI
