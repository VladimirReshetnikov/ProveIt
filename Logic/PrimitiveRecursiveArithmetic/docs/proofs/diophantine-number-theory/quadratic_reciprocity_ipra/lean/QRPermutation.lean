import QRConstructiveList

namespace QR

def natProd : List Nat → Nat
  | [] => 1
  | x :: xs => x * natProd xs

def natSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + natSum xs

theorem perm_prod {xs ys : List Nat} (h : xs.Perm ys) : natProd xs = natProd ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [natProd, ih]
  | swap => simp only [natProd]; ac_rfl
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

theorem perm_sum {xs ys : List Nat} (h : xs.Perm ys) : natSum xs = natSum ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [natSum, ih]
  | swap => simp only [natSum]; ac_rfl
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

theorem natProd_append (xs ys : List Nat) :
    natProd (xs ++ ys) = natProd xs * natProd ys := by
  induction xs with
  | nil => simp [natProd]
  | cons x xs ih => simp [natProd, ih, Nat.mul_assoc]

theorem natSum_append (xs ys : List Nat) :
    natSum (xs ++ ys) = natSum xs + natSum ys := by
  induction xs with
  | nil => simp [natSum]
  | cons x xs ih => simp [natSum, ih, Nat.add_assoc]

theorem natSum_range_succ (f : Nat → Nat) (n : Nat) :
    natSum ((List.range' 1 (n+1)).map f) = natSum ((List.range' 1 n).map f) + f (n+1) := by
  rw [List.range'_1_concat, List.map_append, natSum_append]
  simp [natSum, Nat.add_comm]

theorem natProd_range_succ (f : Nat → Nat) (n : Nat) :
    natProd ((List.range' 1 (n+1)).map f) = natProd ((List.range' 1 n).map f) * f (n+1) := by
  rw [List.range'_1_concat, List.map_append, natProd_append]
  simp [natProd, Nat.add_comm]

/-- A duplicate-free list occupying a list of equal length exhausts it. -/
theorem perm_of_nodup_subset {xs ys : List Nat} (hn : xs.Nodup) (hs : xs ⊆ ys)
    (hl : xs.length = ys.length) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp hl.symm
    subst ys
    exact List.Perm.nil
  | cons x xs ih =>
    have hx : x ∈ ys := hs List.mem_cons_self
    obtain ⟨hxout, hnd⟩ := List.nodup_cons.mp hn
    have hsub : xs ⊆ ys.erase x := by
      intro z hz
      have hne : z ≠ x := by rintro rfl; exact hxout hz
      exact (QR.mem_erase_of_ne hne).mpr (hs (List.mem_cons_of_mem _ hz))
    have hlen : xs.length = (ys.erase x).length := by
      rw [QR.length_erase_of_mem hx]
      simp only [List.length_cons] at hl
      omega
    exact (List.Perm.cons x (ih hnd hsub hlen)).trans (QR.perm_cons_erase hx).symm

/-- An injective endomap of the interval permutes the complete interval. -/
theorem map_range_perm {f : Nat → Nat} (n : Nat)
    (hmap : ∀ i, 0 < i → i ≤ n → 0 < f i ∧ f i ≤ n)
    (hinj : ∀ i j, 0 < i → i ≤ n → 0 < j → j ≤ n → f i = f j → i = j) :
    ((List.range' 1 n).map f).Perm (List.range' 1 n) := by
  have hmem (k : Nat) : k ∈ List.range' 1 n ↔ 0 < k ∧ k ≤ n := by
    rw [List.mem_range'_1]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> omega
  apply perm_of_nodup_subset
  · apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (p := QR.nodup_range_one 1 n)
    intro i j hi hj hij heq
    obtain ⟨hi₁, hi₂⟩ := (hmem i).mp hi
    obtain ⟨hj₁, hj₂⟩ := (hmem j).mp hj
    exact hij (hinj i j hi₁ hi₂ hj₁ hj₂ heq)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    obtain ⟨h₁, h₂⟩ := (hmem x).mp hx
    exact (hmem (f x)).mpr (hmap x h₁ h₂)
  · simp

end QR
