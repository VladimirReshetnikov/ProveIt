import Prefix

namespace BudgetAnalysis.Prefix

/-- none means that no finite prefix suffices. -/
def FitsAt : Option Nat → Nat → Prop
  | none, _ => False
  | some k, n => k ≤ n

/-- For one pair of leaves it suffices to observe any conflicting address. -/
def firstOf : Option Nat → Option Nat → Option Nat
  | none, v => v
  | u, none => u
  | some i, some j => some (min i j)

theorem firstOf_spec (u v : Option Nat) (n : Nat) :
    FitsAt (firstOf u v) n ↔ FitsAt u n ∨ FitsAt v n := by
  cases u <;> cases v <;> simp [firstOf, FitsAt] <;> omega

/-- Every forbidden pair has to be separated. -/
def both : Option Nat → Option Nat → Option Nat
  | some i, some j => some (max i j)
  | _, _ => none

theorem both_spec (u v : Option Nat) (n : Nat) :
    FitsAt (both u v) n ↔ FitsAt u n ∧ FitsAt v n := by
  cases u <;> cases v <;> simp [both, FitsAt] <;> omega

def boundary (u v : Sparse) : List Nat → Option Nat
  | [] => none
  | i :: is =>
    if pairOK (lookup u i) (lookup v i) then boundary u v is
    else firstOf (some (i+1)) (boundary u v is)

theorem boundary_spec (u v : Sparse) (is : List Nat) (n : Nat) :
    FitsAt (boundary u v is) n ↔
      ¬ is.all (fun i => if i < n then pairOK (lookup u i) (lookup v i) else true) = true := by
  induction is with
  | nil => simp [boundary, FitsAt]
  | cons i is ih =>
    have one : FitsAt (some (i+1)) n ↔ i < n := Iff.rfl
    cases h : pairOK (lookup u i) (lookup v i) <;> by_cases hi : i < n <;>
      simp only [boundary, h, Bool.false_eq_true, if_false, if_true, firstOf_spec, one, ih,
        List.all_cons, hi, Bool.false_and, Bool.true_and] <;> simp

def least : List (Sparse × Sparse) → Option Nat
  | [] => some 0
  | (u,v) :: zs => both (boundary u v (u.map Prod.fst)) (least zs)

theorem least_spec (zs : List (Sparse × Sparse)) (n : Nat) :
    FitsAt (least zs) n ↔ safePrefix n zs = true := by
  induction zs with
  | nil => simp [least, FitsAt, safePrefix]
  | cons z zs ih =>
    obtain ⟨u,v⟩ := z
    simp only [least, both_spec, boundary_spec, ih, safePrefix, List.all_cons,
      Bool.and_eq_true, Bool.not_eq_true', prefixOK]
    cases ((List.map Prod.fst u).all
      (fun i => if i < n then pairOK (lookup u i) (lookup v i) else true)) <;> simp

/-- Nonemptiness of the conflicting set for every pair ensures a finite result.
    Whenever least returns a value, it is both sufficient and necessary. -/
theorem least_value {zs : List (Sparse × Sparse)} {k : Nat} (h : least zs = some k)
    (n : Nat) : k ≤ n ↔ safePrefix n zs = true := by
  simpa [h, FitsAt] using least_spec zs n

end BudgetAnalysis.Prefix
