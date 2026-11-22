import Std

namespace QR

/-- Moving the first occurrence of a natural number uses decidable equality. -/
theorem perm_cons_erase {x : Nat} {xs : List Nat} (hx : x ∈ xs) :
    xs.Perm (x :: xs.erase x) := by
  induction xs with
  | nil => contradiction
  | cons y ys ih =>
    by_cases e : y=x
    · subst y
      rw [List.erase_cons_head]
    · rw [List.erase_cons_tail (by simpa using e)]
      have hm := (List.mem_cons.mp hx).resolve_left (Ne.symm e)
      exact (List.Perm.cons y (ih hm)).trans (List.Perm.swap x y _)

/-- Erasure leaves membership of every different number invariant. -/
theorem mem_erase_of_ne {x y : Nat} {xs : List Nat} (hne : x ≠ y) :
    x ∈ xs.erase y ↔ x ∈ xs := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    by_cases e : z=y
    · subst z
      rw [List.erase_cons_head, List.mem_cons]
      exact ⟨Or.inr,fun h => h.resolve_left hne⟩
    · rw [List.erase_cons_tail (by simpa using e),List.mem_cons,List.mem_cons,ih]

theorem length_erase_of_mem {x : Nat} {xs : List Nat} (hm : x ∈ xs) :
    (xs.erase x).length = xs.length - 1 := by
  have h := (perm_cons_erase hm).length_eq
  simp only [List.length_cons] at h
  omega

/-- With no repetitions, erasure deletes exactly the specified element. -/
theorem nodup_mem_erase_iff {x y : Nat} {xs : List Nat} (nd : xs.Nodup) :
    y ∈ xs.erase x ↔ y ≠ x ∧ y ∈ xs := by
  by_cases he : y = x
  · subst y
    by_cases hm : x ∈ xs
    · have hs := (perm_cons_erase hm).nodup_iff.mp nd
      exact ⟨fun h => False.elim ((List.nodup_cons.mp hs).1 h),
        fun h => False.elim (h.1 rfl)⟩
    · have hm' : x ∉ xs.erase x := by
        intro h
        have sub := List.erase_sublist (a:=x) (l:=xs)
        exact hm (sub.subset h)
      exact ⟨fun h => False.elim (hm' h),fun h => False.elim (h.1 rfl)⟩
  · rw [mem_erase_of_ne he]
    exact ⟨fun h => ⟨he,h⟩,And.right⟩

/-- Successive integers form a duplicate-free list. -/
theorem nodup_range_one (start len : Nat) : (List.range' start len).Nodup := by
  induction len generalizing start with
  | zero => exact List.nodup_nil
  | succ len ih =>
    rw [List.range'_succ, List.nodup_cons]
    exact ⟨fun h => by have := List.mem_range'_1.mp h; omega, ih _⟩

end QR
