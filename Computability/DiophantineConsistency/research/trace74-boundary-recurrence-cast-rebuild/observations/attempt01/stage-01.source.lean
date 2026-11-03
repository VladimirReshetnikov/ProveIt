import DiophantineConsistency.ArithmeticPellRecurrence

/-! UNCHECKED DRAFT. A standard finite Pell recurrence and its compatibility
with the represented recurrence in an arbitrary IΣ₁ model. No finite seed
inequality, concrete graph zero, or fixed-port consequence is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74BoundaryRecurrenceCast
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPellRecurrence

/-- The offset parameter `b` corresponds to the Pell base `b + 2`. -/
def xy : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (1, 0)
  | n+1, b =>
      let prev := xy n b
      ((b+2)*prev.1 + (b+1)*(b+3)*prev.2,
       prev.1 + (b+2)*prev.2)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Standard finite iterations embed in every model with the same coordinates. -/
theorem xy_cast (n b : ℕ) :
    xcoord (n : V) (b : V) = ((xy n b).1 : V) ∧
    ycoord (n : V) (b : V) = ((xy n b).2 : V) := by
  induction n with
  | zero => simp [xy]
  | succ n ih =>
      constructor
      · rw [Nat.cast_succ, x_succ, ih.1, ih.2]
        simp only [xy, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, delta]
      · rw [Nat.cast_succ, y_succ, ih.1, ih.2]
        simp only [xy, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

#print axioms Trace74BoundaryRecurrenceCast.xy_cast
end Trace74BoundaryRecurrenceCast
