import Mathlib

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerRadixValue : {n : ℕ} → (Fin n → ℕ) → (Fin n → ℤ) → ℤ
  | 0, _, _ => 0
  | n + 1, R, x => x 0 + (R 0 : ℤ) * integerRadixValue (fun i : Fin n => R i.succ) (fun i => x i.succ)

theorem integerRadixValue_zero {n : ℕ} (R : Fin n → ℕ) :
    integerRadixValue R 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (0 : ℤ) + (R 0 : ℤ) * integerRadixValue (fun i : Fin n => R i.succ) 0 = 0
      rw [ih, mul_zero, add_zero]

theorem integerRadixValue_add {n : ℕ} (R : Fin n → ℕ) (x y : Fin n → ℤ) :
    integerRadixValue R (x + y) = integerRadixValue R x + integerRadixValue R y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [integerRadixValue, Pi.add_apply]
      rw [show (fun i : Fin n => x i.succ + y i.succ) =
        (fun i => x i.succ) + (fun i => y i.succ) from rfl, ih]
      ring

def integerRadixHom {n : ℕ} (R : Fin n → ℕ) : (Fin n → ℤ) →+ ℤ where
  toFun := integerRadixValue R
  map_zero' := integerRadixValue_zero R
  map_add' := integerRadixValue_add R

theorem integerRadixValue_bounds {n : ℕ} (R : Fin n → ℕ) (x : Fin n → ℤ)
    (hx : ∀ i, 0 ≤ x i ∧ x i < (R i : ℤ)) :
    0 ≤ integerRadixValue R x ∧ integerRadixValue R x < ((∏ i, R i : ℕ) : ℤ) := by
  induction n with
  | zero => simp [integerRadixValue]
  | succ n ih =>
      have h0 := hx 0
      have ht := ih (fun i => R i.succ) (fun i => x i.succ) (fun i => hx i.succ)
      have hm := mul_le_mul_of_nonneg_left
        (show integerRadixValue (fun i : Fin n => R i.succ) (fun i => x i.succ) ≤
          ((∏ i : Fin n, R i.succ : ℕ) : ℤ) - 1 by omega)
        (Nat.cast_nonneg (R 0) : (0 : ℤ) ≤ R 0)
      rw [integerRadixValue, Fin.prod_univ_succ, Nat.cast_mul]
      constructor
      · exact add_nonneg h0.1 (mul_nonneg (Nat.cast_nonneg _) ht.1)
      · nlinarith

theorem integerRadixValue_injective_on_digits {n : ℕ} (R : Fin n → ℕ)
    (x y : Fin n → ℤ) (hx : ∀ i, 0 ≤ x i ∧ x i < (R i : ℤ))
    (hy : ∀ i, 0 ≤ y i ∧ y i < (R i : ℤ))
    (he : integerRadixValue R x = integerRadixValue R y) : x = y := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
      have hx0 := hx 0
      have hy0 := hy 0
      have hR : (R 0 : ℤ) ≠ 0 := ne_of_gt (lt_of_le_of_lt hx0.1 hx0.2)
      have h0 : x 0 = y 0 := by
        have h := congrArg (fun z : ℤ => z % (R 0 : ℤ)) he
        simpa only [integerRadixValue, Int.add_emod, Int.mul_emod, Int.emod_self,
          zero_mul, Int.zero_emod, add_zero, Int.emod_eq_of_lt hx0.1 hx0.2,
          Int.emod_eq_of_lt hy0.1 hy0.2] using h
      have ht : integerRadixValue (fun i : Fin n => R i.succ) (fun i => x i.succ) =
          integerRadixValue (fun i : Fin n => R i.succ) (fun i => y i.succ) := by
        apply mul_left_cancel₀ hR
        simpa only [integerRadixValue, h0, add_left_cancel_iff] using he
      have hh := ih (fun i => R i.succ) (fun i => x i.succ) (fun i => y i.succ)
        (fun i => hx i.succ) (fun i => hy i.succ) ht
      funext i
      exact Fin.cases h0 (fun j => congrFun hh j) i

end Erdos3

end

end OAI
