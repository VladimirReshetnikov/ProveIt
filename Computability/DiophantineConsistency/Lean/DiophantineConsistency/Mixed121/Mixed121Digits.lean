import DiophantineConsistency.Mixed121.Mixed121Kernel
import DiophantineConsistency.ModelDigitTransfer
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

/-! # The 121x8801 clause coefficients in radix-four digit form

Every clause coefficient of `Mixed121Kernel` is `1 + 2^10·Σ_{k<44} d_k 4^k`.
The digit `d_{10t+j}` is bit `j` of `x_t + 512`, and the four anchor digits
`d_40, …, d_43` are `1`. The extra weight `W k` is the single digit `2^10·4^k`.
This is the shape `Mixed121Decoder.decode` consumes; `clause_cast` transports
it into any model of `𝗜𝚺₁`. The identities are proved for an arbitrary tile,
so no row table is evaluated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Mixed121Digits
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency.ModelDigitTransfer
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Bit `j` of `x + 512`. -/
def bit (x j : ℕ) : ℕ := (x+512)/2^j % 2

/-- The 44 radix-four digits of a tile's clause coefficient. -/
def digit (tile : ℕ × ℕ × ℕ × ℕ) (k : ℕ) : ℕ :=
  if k < 10 then bit tile.1 k
  else if k < 20 then bit tile.2.1 (k-10)
  else if k < 30 then bit tile.2.2.1 (k-20)
  else if k < 40 then bit tile.2.2.2 (k-30)
  else 1

theorem digit_le_one (tile : ℕ × ℕ × ℕ × ℕ) (k : ℕ) : digit tile k ≤ 1 := by
  unfold digit bit
  split_ifs <;> omega

private theorem field_eq (x t : ℕ) :
    Mixed121Kernel.field x t =
      2^10 * ∑ j ∈ Finset.range 10, bit x j * 4^(10*t+j) := by
  rw [Mixed121Kernel.field, Finset.mul_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold Mixed121Kernel.W bit
  rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul, pow_add]
  ring

private theorem block (tile : ℕ × ℕ × ℕ × ℕ) (n : ℕ) (x : ℕ)
    (hx : ∀ j < 10, digit tile (n + j) = bit x j) :
    ∑ j ∈ Finset.range 10, digit tile (n + j) * 4^(n+j) =
      ∑ j ∈ Finset.range 10, bit x j * 4^(n+j) :=
  Finset.sum_congr rfl fun j hj => by rw [hx j (Finset.mem_range.mp hj)]

/-- The clause coefficient in radix-four digit form. -/
theorem clause_digits (tile : ℕ × ℕ × ℕ × ℕ) :
    Mixed121Kernel.clause tile =
      1 + 2^10 * ∑ k ∈ Finset.range 44, digit tile k * 4^k := by
  obtain ⟨x0, x1, x2, x3⟩ := tile
  have e44 : (44:ℕ) = 10 + 10 + 10 + 10 + 4 := rfl
  rw [e44, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add,
    Finset.sum_range_add]
  have b0 := block (x0, x1, x2, x3) 0 x0 fun j hj => by
    simp only [digit, Nat.zero_add, if_pos hj]
  have b1 := block (x0, x1, x2, x3) 10 x1 fun j hj => by
    simp only [digit, if_neg (show ¬ 10 + j < 10 by omega), if_pos (show 10 + j < 20 by omega),
      Nat.add_sub_cancel_left]
  have b2 := block (x0, x1, x2, x3) 20 x2 fun j hj => by
    simp only [digit, if_neg (show ¬ 20 + j < 10 by omega), if_neg (show ¬ 20 + j < 20 by omega),
      if_pos (show 20 + j < 30 by omega), Nat.add_sub_cancel_left]
  have b3 := block (x0, x1, x2, x3) 30 x3 fun j hj => by
    simp only [digit, if_neg (show ¬ 30 + j < 10 by omega), if_neg (show ¬ 30 + j < 20 by omega),
      if_neg (show ¬ 30 + j < 30 by omega), if_pos (show 30 + j < 40 by omega),
      Nat.add_sub_cancel_left]
  have b4 : ∑ x ∈ Finset.range 4, digit (x0, x1, x2, x3) (40 + x) * 4^(40 + x) =
      4^40 + 4^41 + 4^42 + 4^43 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, digit]
    norm_num
  simp only [Nat.reduceAdd, Nat.zero_add] at b0 b1 b2 b3 ⊢
  rw [b0, b1, b2, b3, b4]
  simp only [Mixed121Kernel.clause, field_eq, Mixed121Kernel.W, Nat.mul_zero, Nat.zero_add,
    Nat.reduceMul, Nat.reduceAdd]
  ring

theorem W_digit (k : ℕ) : Mixed121Kernel.W k = 2^10 * 4^k := by
  unfold Mixed121Kernel.W
  rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul, pow_add]

private theorem exp_two' : Exp.exp (2:V) = 4 := by
  rw [show (2:V) = 1 + 1 by norm_num, exp_succ, exp_one]; norm_num

private theorem exp_ten' : Exp.exp (10:V) = 1024 := by
  have h : ∀ n : ℕ, Exp.exp (n:V) = (2:V)^n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_add, Nat.cast_one, exp_succ, ih, pow_succ, mul_comm]
  have := h 10
  norm_num only [Nat.cast_ofNat] at this
  rw [this]

/-- The clause coefficient in a model, in the decoder's `dsum` form. -/
theorem clause_cast (tile : ℕ × ℕ × ℕ × ℕ) :
    ((Mixed121Kernel.clause tile : ℕ) : V) =
      1 + Exp.exp 10 * dsum (Exp.exp 2) (fun k => (digit tile k : V)) 44 := by
  rw [clause_digits, exp_ten', exp_two']
  simp only [dsum, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow,
    Nat.cast_ofNat]
  norm_num

/-- An extra weight in a model: one radix-four digit above `2^10`. -/
theorem W_cast (k : ℕ) :
    ((Mixed121Kernel.W k : ℕ) : V) = Exp.exp 10 * (Exp.exp 2)^k := by
  rw [W_digit, exp_ten', exp_two']
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  norm_num

/-- The clause-target part of the native mask, `μ = 1022 + Σ_{k<44} W k`,
in the decoder's mask form `(2^10 − 2) + 2^10·Σ_{k<44} 4^k`. -/
theorem mu_cast :
    ((1022 + ∑ k ∈ Finset.range 44, Mixed121Kernel.W k : ℕ) : V) =
      (Exp.exp 10 - 2) + Exp.exp 10 * dsum (Exp.exp 2) (fun _ => 1) 44 := by
  have h2 : (Exp.exp (10:V)) - 2 = 1022 := by
    rw [exp_ten']
    exact tsub_eq_of_eq_add (by norm_num)
  rw [h2]
  simp only [W_digit, dsum, Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, exp_ten', exp_two', one_mul, Finset.mul_sum]
  norm_num
end Mixed121Digits
#print axioms Mixed121Digits.digit_le_one
#print axioms Mixed121Digits.clause_digits
#print axioms Mixed121Digits.clause_cast
#print axioms Mixed121Digits.W_cast
#print axioms Mixed121Digits.mu_cast
