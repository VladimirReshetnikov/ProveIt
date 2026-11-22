import BertrandSearch

namespace Bertrand

/-- Product over the inclusive natural interval [1,k]. -/
def prod (f : Nat → Nat) : Nat → Nat
  | 0 => 1
  | k+1 => prod f k * f (k+1)

def primeFactor (p : Nat) := if primeB p then p else 1
def primorial (m : Nat) := prod primeFactor m

theorem prod_mono {f g : Nat → Nat} (k : Nat) (h : ∀ p, 1 ≤ p → p ≤ k → f p ≤ g p) :
    prod f k ≤ prod g k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    exact Nat.mul_le_mul (ih fun p hp hk => h p hp (by omega)) (h (k+1) (by omega) (by omega))

theorem prod_mul (f g : Nat → Nat) (k : Nat) :
    prod (fun p => f p * g p) k = prod f k * prod g k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [prod, ih]; ac_rfl

theorem prod_one (k : Nat) : prod (fun _ => 1) k = 1 := by
  induction k <;> simp_all [prod]

theorem prod_const (x k : Nat) : prod (fun _ => x) k = x^k := by
  induction k <;> simp_all [prod, Nat.pow_succ]

theorem prod_cut (f : Nat → Nat) {m k : Nat} (hm : m ≤ k) :
    prod (fun p => if p ≤ m then f p else 1) k = prod f m := by
  induction k with
  | zero => simp [show m = 0 by omega, prod]
  | succ k ih =>
    by_cases h : m = k+1
    · subst m
      have lower := prod_mono k (f := f) (g := fun p => if p ≤ k+1 then f p else 1)
        (fun p _ hp => by simp [show p ≤ k+1 by omega])
      have upper := prod_mono k (g := f) (f := fun p => if p ≤ k+1 then f p else 1)
        (fun p _ hp => by simp [show p ≤ k+1 by omega])
      simp [prod, Nat.le_antisymm upper lower]
    · simp only [prod, if_neg (show ¬ k+1 ≤ m by omega), Nat.mul_one]
      exact ih (by omega)

theorem prod_single (x : Nat) {j k : Nat} (hj : 0 < j) (hk : j ≤ k) :
    prod (fun p => if p = j then x else 1) k = x := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : k+1 = j
    · subst j
      have eq : prod (fun p => if p = k+1 then x else 1) k = prod (fun _ => 1) k := by
        apply Nat.le_antisymm <;> apply prod_mono <;> intro p _ hp <;> simp [show p ≠ k+1 by omega]
      rw [prod, eq, prod_one, if_pos rfl, Nat.one_mul]
    · simp only [prod, if_neg h, Nat.mul_one]
      exact ih (by omega)

end Bertrand
