import DiophantineConsistency.ArithmeticBinaryPopulation

/-! Casts of standard natural numerals in models of IΣ1. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticStandardCasts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cast_exp (n : ℕ) : Exp.exp (n:V) = ((2^n : ℕ) : V) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, exp_succ, ih]
    push_cast
    ring

theorem cast_mod (a b : ℕ) : ((a % b : ℕ) : V) = (a:V) % (b:V) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · have he : (a:V) = (b:V) * ((a / b : ℕ) : V) + ((a % b : ℕ) : V) := by
      exact_mod_cast (Nat.div_add_mod a b).symm
    have hr : ((a % b : ℕ) : V) < (b:V) := by exact_mod_cast Nat.mod_lt a hb
    have hb' : (0:V) < (b:V) := by exact_mod_cast hb
    rw [he, mod_mul_add' _ _ hb', mod_eq_self_of_lt hr]

theorem cast_div (a b : ℕ) : ((a / b : ℕ) : V) = (a:V) / (b:V) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · have he : (a:V) = (b:V) * ((a / b : ℕ) : V) + ((a % b : ℕ) : V) := by
      exact_mod_cast (Nat.div_add_mod a b).symm
    have hr : ((a % b : ℕ) : V) < (b:V) := by exact_mod_cast Nat.mod_lt a hb
    rw [he, div_mul_add' _ _ hr]


end DiophantineConsistency.ArithmeticStandardCasts
