import Std

/-!
Finite Bell arithmetic. All theorems below are metatheoretic Lean proofs.
They are not claims that a ConciseIPRA.Prf object has been constructed.
No real numbers, infinite sums, noncomputable definitions, or classical
choice are used. See the paper for the separate object-theory translation.
-/

namespace BellIPRA

def sum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sum f n + f n

@[simp] theorem sum_zero (f : Nat → Nat) : sum f 0 = 0 := rfl
@[simp] theorem sum_succ (f : Nat → Nat) (n : Nat) :
    sum f (n + 1) = sum f n + f n := rfl

theorem sum_congr {f g : Nat → Nat} (n : Nat)
    (h : ∀ k, k < n → f k = g k) : sum f n = sum g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sum_succ, sum_succ, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]

theorem sum_add (f g : Nat → Nat) (n : Nat) :
    sum (fun k => f k + g k) n = sum f n + sum g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum_succ, ih]; omega

theorem sum_shift (f : Nat → Nat) (n : Nat) :
    sum f (n + 1) = f 0 + sum (fun k => f (k + 1)) n := by
  induction n with
  | zero => simp [sum]
  | succ n ih => rw [sum_succ, ih, sum_succ]; omega

theorem sum_mono {f g : Nat → Nat} (n : Nat)
    (h : ∀ k, k < n → f k ≤ g k) : sum f n ≤ sum g n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    exact Nat.add_le_add (ih (fun k hk => h k (Nat.lt_succ_of_lt hk))) (h n (Nat.lt_succ_self n))

theorem sum_mul (c : Nat) (f : Nat → Nat) (n : Nat) :
    sum (fun k => c * f k) n = c * sum f n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_succ, sum_succ, ih, Nat.mul_add]

def stirling : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling n (k + 1) + stirling n k

def bell (n : Nat) : Nat := sum (stirling n) (n + 1)

@[simp] theorem stirling_zero_zero : stirling 0 0 = 1 := rfl
@[simp] theorem stirling_zero_succ (k : Nat) : stirling 0 (k + 1) = 0 := rfl
@[simp] theorem stirling_succ_zero (n : Nat) : stirling (n + 1) 0 = 0 := rfl
theorem stirling_step (n k : Nat) :
    stirling (n + 1) (k + 1) = (k + 1) * stirling n (k + 1) + stirling n k := rfl

theorem stirling_above (n k : Nat) (h : n < k) : stirling n k = 0 := by
  induction n generalizing k with
  | zero => cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih => cases k with
    | zero => omega
    | succ k =>
      rw [stirling_step, ih (k + 1) (by omega), ih k (by omega)]
      simp

@[simp] theorem stirling_diagonal (n : Nat) : stirling n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stirling_step, stirling_above n (n + 1) (Nat.lt_succ_self n), ih]; rfl

@[simp] theorem stirling_one (n : Nat) : stirling (n + 1) 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stirling_step, ih, stirling_succ_zero]

theorem bell_positive (n : Nat) : 0 < bell n := by
  unfold bell
  rw [sum_succ, stirling_diagonal]
  omega

theorem bell_weighted (n : Nat) :
    bell (n + 1) = sum (fun k => (k + 1) * stirling n k) (n + 1) := by
  have habove : stirling n (n + 1) = 0 := stirling_above n (n + 1) (Nat.lt_succ_self n)
  have hshift : sum (fun k => (k + 1) * stirling n (k + 1)) (n + 1) =
      sum (fun k => k * stirling n k) (n + 1) := by
    have h := sum_shift (fun k => k * stirling n k) (n + 1)
    simp only [Nat.zero_mul, Nat.zero_add] at h
    rw [← h, sum_succ, habove, Nat.mul_zero, Nat.add_zero]
  unfold bell
  rw [sum_shift, stirling_succ_zero, Nat.zero_add]
  change sum (fun k => (k + 1) * stirling n (k + 1) + stirling n k) (n + 1) = _
  rw [sum_add, hshift, ← sum_add]
  exact sum_congr (n + 1) (fun k _ => by rw [Nat.add_mul, Nat.one_mul])

theorem bell_monotone_step (n : Nat) : bell n ≤ bell (n + 1) := by
  rw [bell_weighted]
  apply sum_mono
  intro k _
  have h := Nat.mul_le_mul_right (stirling n k) (Nat.le_add_left 1 k)
  simpa using h

theorem bell_step_upper (n : Nat) : bell (n + 1) ≤ (n + 1) * bell n := by
  rw [bell_weighted, bell, ← sum_mul]
  apply sum_mono
  intro k hk
  exact Nat.mul_le_mul_right (stirling n k) (by omega)

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem bell_le_factorial (n : Nat) : bell n ≤ factorial n := by
  induction n with
  | zero => exact Nat.le_refl 1
  | succ n ih =>
    exact Nat.le_trans (bell_step_upper n) (Nat.mul_le_mul_left (n + 1) ih)

theorem bell_zero : bell 0 = 1 := rfl
theorem bell_one : bell 1 = 1 := rfl
theorem bell_two : bell 2 = 2 := rfl
theorem bell_three : bell 3 = 5 := rfl
theorem bell_four : bell 4 = 15 := rfl
theorem bell_five : bell 5 = 52 := rfl
theorem bell_six : bell 6 = 203 := rfl
theorem bell_seven : bell 7 = 877 := rfl
theorem bell_eight : bell 8 = 4140 := rfl
theorem bell_nine : bell 9 = 21147 := rfl
theorem bell_ten : bell 10 = 115975 := rfl

end BellIPRA
